"""Tests for ACE Runtime with stability + lawfulness guarantees."""

import pytest
from atlas.aep.ace_runtime import (
    ACERuntimeState,
    ACERuntime,
    BoundaryGroup,
    FairSchedule,
    compute_kkt_certificate,
    compute_operator_norm,
    verify_contraction,
    compute_state_distance,
    compute_update,
    generate_subgroup_certificate,
    create_audit_bundle,
    ATLAS_CLASSES,
    ATLAS_COORDINATES,
    NUM_ANCHORS,
    Z2_GROUP_ORDER,
)
from atlas.aep.ace import Budgets


# ---------------------------
# KKT Certificate Tests
# ---------------------------


def test_kkt_certificate_valid_projection():
    """Test KKT certificate for a valid projection."""
    # Create simple test case
    Q = 1000
    w_star_Q = [100, 200, 300]
    budgets = Budgets(
        b=[1, 1, 1],
        a=[1, 1, 1],
        limit1_Q=700,
        limit2_Q=700,
        Q=Q,
    )

    from atlas.aep.ace import ProjResult

    proj_result = ProjResult(
        w_star_Q=w_star_Q,
        lam_Q=0,
        mu_Q=0,
        sum1=600,
        sum2=600,
    )

    cert = compute_kkt_certificate(w_star_Q, budgets, proj_result)
    assert cert.primal_feasible
    assert cert.dual_feasible
    assert cert.stationarity_gap == 0


def test_kkt_certificate_infeasible():
    """Test KKT certificate when constraints are violated."""
    Q = 1000
    w_star_Q = [100, 200, 300]
    budgets = Budgets(
        b=[1, 1, 1],
        a=[1, 1, 1],
        limit1_Q=500,  # Too tight
        limit2_Q=500,
        Q=Q,
    )

    from atlas.aep.ace import ProjResult

    proj_result = ProjResult(
        w_star_Q=w_star_Q,
        lam_Q=100,
        mu_Q=100,
        sum1=600,  # Exceeds limit
        sum2=600,
    )

    cert = compute_kkt_certificate(w_star_Q, budgets, proj_result)
    assert not cert.primal_feasible
    assert not cert.is_valid()


# ---------------------------
# Contraction Tests
# ---------------------------


def test_compute_operator_norm():
    """Test operator norm computation."""
    Q = 1000

    # Identity matrix (scaled by Q)
    I = [[Q if i == j else 0 for j in range(3)] for i in range(3)]
    norm = compute_operator_norm(I, Q)
    assert norm == Q  # ∥I∥ = 1

    # Contraction matrix K = 0.8 * I
    K = [[800 if i == j else 0 for j in range(3)] for i in range(3)]
    norm = compute_operator_norm(K, Q)
    assert norm == 800  # ∥K∥ = 0.8


def test_verify_contraction():
    """Test contraction verification."""
    Q = 1000
    eps_t = 200  # Gap = 0.2

    # K with norm 0.7 < 1 - 0.2 = 0.8 ✓
    K_norm_ok = 700
    assert verify_contraction(K_norm_ok, eps_t, Q)

    # K with norm 0.9 > 1 - 0.2 = 0.8 ✗
    K_norm_bad = 900
    assert not verify_contraction(K_norm_bad, eps_t, Q)


def test_compute_state_distance():
    """Test ℓ₁ distance computation."""
    Q = 1000
    T1 = [100, 200, 300]
    T2 = [110, 190, 320]

    dist = compute_state_distance(T1, T2, Q)
    # |100-110| + |200-190| + |300-320| = 10 + 10 + 20 = 40
    assert dist == 40


# ---------------------------
# Update Law Tests
# ---------------------------


def test_compute_update_identity():
    """Test update law with identity operator."""
    Q = 1000
    T_t = [100, 200, 300]
    F = [50, 50, 50]

    # K = I (identity)
    I = [[Q if i == j else 0 for j in range(3)] for i in range(3)]

    T_next = compute_update(T_t, F, I, Q)
    # T_{t+1} = F + I @ T_t = F + T_t
    expected = [150, 250, 350]
    assert T_next == expected


def test_compute_update_contraction():
    """Test update law with contraction."""
    Q = 1000
    T_t = [1000, 2000, 3000]
    F = [0, 0, 0]  # Origin as fixed point

    # K = 0.5 * I (contraction toward origin)
    K = [[500 if i == j else 0 for j in range(3)] for i in range(3)]

    T_next = compute_update(T_t, F, K, Q)
    # T_{t+1} = 0 + 0.5 * T_t = 0.5 * T_t
    expected = [500, 1000, 1500]
    assert T_next == expected


# ---------------------------
# ACE Runtime Tests
# ---------------------------


def test_ace_runtime_single_step():
    """Test single ACE runtime step."""
    Q = 1000

    # Small state for testing
    state = ACERuntimeState(
        T=[100, 200, 300, 400],
        F=[0, 0, 0, 0],
        Q=Q,
    )

    runtime = ACERuntime(state)

    # Proposal
    w_proposal = [50, 100, 150, 200]

    # Budgets
    budgets = Budgets(
        b=[1, 1, 1, 1],
        a=[1, 1, 1, 1],
        limit1_Q=600,
        limit2_Q=600,
        Q=Q,
    )

    # Norms for acceptance
    B_norms_Q = [100, 100, 100, 100]

    # Contraction operator (0.8 * I)
    eps_t = 200  # Gap = 0.2, so max norm = 0.8
    K_t = [[800 if i == j else 0 for j in range(4)] for i in range(4)]

    success, error = runtime.step(w_proposal, budgets, B_norms_Q, eps_t, K_t, fail_closed=True)

    assert success, f"Step failed: {error}"
    assert state.step == 1
    assert len(state.kkt_certificates) == 1
    assert len(state.contraction_history) == 1


def test_ace_runtime_convergence():
    """Test ACE runtime convergence over multiple steps."""
    Q = 1000

    # Initial state away from fixed point
    state = ACERuntimeState(
        T=[Q, Q, Q, Q],
        F=[0, 0, 0, 0],  # Fixed point at origin
        Q=Q,
        convergence_threshold=10,
    )

    runtime = ACERuntime(state)

    # Strong contraction (0.5 * I)
    eps_t = 500
    K_t = [[500 if i == j else 0 for j in range(4)] for i in range(4)]

    budgets = Budgets(
        b=[1, 1, 1, 1],
        a=[1, 1, 1, 1],
        limit1_Q=5000,
        limit2_Q=5000,
        Q=Q,
    )
    B_norms_Q = [100, 100, 100, 100]

    # Run multiple steps
    for _ in range(15):
        w_proposal = [0, 0, 0, 0]  # No external input
        success, error = runtime.step(w_proposal, budgets, B_norms_Q, eps_t, K_t, fail_closed=True)
        assert success, f"Step failed: {error}"

        if state.converged:
            break

    # Should converge (exponential decay)
    assert state.converged or state.contraction_history[-1].delta_T < 100


def test_ace_runtime_fail_closed():
    """Test fail-closed semantics."""
    Q = 1000

    state = ACERuntimeState(
        T=[100, 200, 300, 400],
        F=[0, 0, 0, 0],
        Q=Q,
    )

    runtime = ACERuntime(state)

    # Non-contractive operator (norm > 1 - ε)
    eps_t = 100  # Max allowed norm = 0.9
    K_t = [[950 if i == j else 0 for j in range(4)] for i in range(4)]  # Norm = 0.95 > 0.9

    budgets = Budgets(b=[1, 1, 1, 1], a=[1, 1, 1, 1], limit1_Q=1000, limit2_Q=1000, Q=Q)
    B_norms_Q = [100, 100, 100, 100]
    w_proposal = [10, 10, 10, 10]

    # Should fail with fail_closed=True
    success, error = runtime.step(w_proposal, budgets, B_norms_Q, eps_t, K_t, fail_closed=True)

    assert not success
    assert "contraction" in error.lower()


def test_cauchy_convergence_certificate():
    """Test Cauchy convergence certificate generation."""
    Q = 1000

    state = ACERuntimeState(
        T=[Q, Q],
        F=[0, 0],
        Q=Q,
    )

    runtime = ACERuntime(state)

    # Run contractive steps
    eps_t = 300
    K_t = [[700 if i == j else 0 for j in range(2)] for i in range(2)]
    budgets = Budgets(b=[1, 1], a=[1, 1], limit1_Q=3000, limit2_Q=3000, Q=Q)
    B_norms_Q = [100, 100]

    for _ in range(10):
        w_proposal = [0, 0]
        runtime.step(w_proposal, budgets, B_norms_Q, eps_t, K_t)

    cert = runtime.get_cauchy_convergence_certificate()

    assert cert["all_contractive"]
    assert cert["total_steps"] == 10
    assert cert["convergence_rate"] < Q  # Should be decreasing


# ---------------------------
# Boundary Group Tests
# ---------------------------


def test_boundary_group_pack_unpack():
    """Test pack/unpack for boundary group."""
    bg = BoundaryGroup()

    # Test round-trip
    for p in [0, 7, 8, 16, 24, 32, 40, 47]:
        for b in [0, 1, 127, 255]:
            r, idx = bg.pack(p, b)
            p2, b2 = bg.unpack(r, idx)
            assert (p, b) == (p2, b2)


def test_boundary_group_anchors():
    """Test anchor points."""
    bg = BoundaryGroup()
    anchors = bg.get_anchors()

    assert len(anchors) == NUM_ANCHORS
    assert anchors == [(0, 0), (8, 0), (16, 0), (24, 0), (32, 0), (40, 0)]


def test_boundary_group_action():
    """Test (Z/2)^11 action."""
    bg = BoundaryGroup()

    # Identity action
    p, b = 8, 100
    p_new, b_new = bg.act_U(p, b, 0)
    assert (p_new, b_new) == (p, b)

    # Non-trivial action
    p_new, b_new = bg.act_U(8, 0, 1)
    assert (p_new, b_new) != (8, 0)

    # Action is invertible
    for u in [1, 7, 255, 1023]:
        u_inv = (Z2_GROUP_ORDER - u) % Z2_GROUP_ORDER
        p_mid, b_mid = bg.act_U(8, 0, u)
        p_back, b_back = bg.act_U(p_mid, b_mid, u_inv)
        assert (p_back, b_back) == (8, 0)


def test_subgroup_certificate():
    """Test subgroup certificate generation."""
    bg = BoundaryGroup()
    cert = generate_subgroup_certificate(bg)

    assert cert["valid"]
    assert cert["group_order"] == Z2_GROUP_ORDER
    assert cert["num_orbits"] == NUM_ANCHORS
    assert cert["total_elements"] == 48 * 256


def test_boundary_group_freeness():
    """Test freeness of action (no fixed points except identity)."""
    bg = BoundaryGroup()

    # Check that non-identity elements have no fixed points
    for u in [1, 2, 3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047]:
        for anchor_p, anchor_b in bg.get_anchors():
            p_new, b_new = bg.act_U(anchor_p, anchor_b, u)
            assert (p_new, b_new) != (anchor_p, anchor_b), f"Fixed point for u={u} at anchor ({anchor_p}, {anchor_b})"


def test_boundary_group_orbit_sizes():
    """Test that each orbit has exactly 2048 elements."""
    bg = BoundaryGroup()

    for anchor_p, anchor_b in bg.get_anchors():
        orbit = set()
        for u in range(Z2_GROUP_ORDER):
            p, b = bg.act_U(anchor_p, anchor_b, u)
            orbit.add((p, b))

        assert len(orbit) == Z2_GROUP_ORDER, f"Orbit size {len(orbit)} != {Z2_GROUP_ORDER} for anchor ({anchor_p}, {anchor_b})"


# ---------------------------
# Fair Schedule Tests
# ---------------------------


def test_fair_schedule_phi():
    """Test Φ transformation."""
    schedule = FairSchedule()

    # Test single application
    p, b = 0, 0
    p_new, b_new = schedule.phi(p, b)
    assert (p_new, b_new) == (16, 1)


def test_fair_schedule_period():
    """Test that Φ^768 = identity on anchors."""
    schedule = FairSchedule()
    bg = BoundaryGroup()
    anchors = bg.get_anchors()

    assert schedule.verify_period(anchors)


def test_fair_schedule_generation():
    """Test schedule generation."""
    schedule = FairSchedule()

    # Generate schedule from anchor
    seq = schedule.generate_schedule(0, 0, 10)
    assert len(seq) == 10
    assert seq[0] == (0, 0)
    assert seq[1] == (16, 1)


# ---------------------------
# Audit Bundle Tests
# ---------------------------


def test_create_audit_bundle():
    """Test audit bundle creation."""
    Q = 1000

    state = ACERuntimeState(
        T=[Q, Q],
        F=[0, 0],
        Q=Q,
    )

    runtime = ACERuntime(state)

    # Run a few steps
    eps_t = 300
    K_t = [[700 if i == j else 0 for j in range(2)] for i in range(2)]
    budgets = Budgets(b=[1, 1], a=[1, 1], limit1_Q=3000, limit2_Q=3000, Q=Q)
    B_norms_Q = [100, 100]

    for _ in range(5):
        w_proposal = [0, 0]
        runtime.step(w_proposal, budgets, B_norms_Q, eps_t, K_t)

    # Create audit bundle
    bg = BoundaryGroup()
    schedule = FairSchedule()
    bundle = create_audit_bundle(state, bg, schedule)

    assert bundle["audit_version"] == "1.0"
    assert bundle["runtime_steps"] == 5
    assert len(bundle["kkt_certificates"]) == 5
    assert len(bundle["contraction_history"]) == 5
    assert bundle["subgroup_certificate"]["valid"]
    assert bundle["schedule_verification"]["valid"]
    assert bundle["petc_ledger"]["valid"]
    assert bundle["lattice_structure"]["classes"] == ATLAS_CLASSES
    assert bundle["lattice_structure"]["coordinates"] == ATLAS_COORDINATES


# ---------------------------
# Integration Tests
# ---------------------------


def test_full_ace_runtime_workflow():
    """Test complete ACE runtime workflow with all components."""
    Q = 1000

    # Initialize with actual lattice dimensions (but small for testing)
    # In production, this would be 96 * 12288
    small_dim = 100
    state = ACERuntimeState(
        T=[Q] * small_dim,
        F=[0] * small_dim,
        Q=Q,
        convergence_threshold=50,
    )

    runtime = ACERuntime(state)

    # Setup contraction
    eps_t = 400  # Gap = 0.4
    K_t = [[600 if i == j else 0 for j in range(small_dim)] for i in range(small_dim)]

    budgets = Budgets(
        b=[1] * small_dim,
        a=[1] * small_dim,
        limit1_Q=Q * small_dim,
        limit2_Q=Q * small_dim,
        Q=Q,
    )
    B_norms_Q = [100] * small_dim

    # Run runtime for several steps
    num_steps = 10
    for step in range(num_steps):
        w_proposal = [0] * small_dim
        success, error = runtime.step(w_proposal, budgets, B_norms_Q, eps_t, K_t, fail_closed=True)
        assert success, f"Step {step} failed: {error}"

    # Verify state
    assert state.step == num_steps
    assert len(state.kkt_certificates) == num_steps
    assert len(state.contraction_history) == num_steps
    assert state.petc_ledger.verify()

    # All steps should be contractive
    assert all(m.is_contractive() for m in state.contraction_history)

    # Generate certificates
    cauchy_cert = runtime.get_cauchy_convergence_certificate()
    assert cauchy_cert["all_contractive"]

    # Generate audit bundle
    bg = BoundaryGroup()
    schedule = FairSchedule()
    audit = create_audit_bundle(state, bg, schedule)

    assert audit["subgroup_certificate"]["valid"]
    assert audit["schedule_verification"]["valid"]
    assert audit["petc_ledger"]["valid"]


def test_ace_runtime_with_boundary_schedule():
    """Test ACE runtime integrated with boundary group and schedule."""
    Q = 1000
    bg = BoundaryGroup()
    schedule = FairSchedule()

    # Use anchor as starting point
    anchors = bg.get_anchors()
    start_p, start_b = anchors[0]

    # Generate schedule
    coord_schedule = schedule.generate_schedule(start_p, start_b, 20)

    # Small runtime for testing
    state = ACERuntimeState(
        T=[Q, Q, Q, Q],
        F=[0, 0, 0, 0],
        Q=Q,
    )

    runtime = ACERuntime(state)

    eps_t = 300
    K_t = [[700 if i == j else 0 for j in range(4)] for i in range(4)]
    budgets = Budgets(b=[1, 1, 1, 1], a=[1, 1, 1, 1], limit1_Q=5000, limit2_Q=5000, Q=Q)
    B_norms_Q = [100, 100, 100, 100]

    # Run steps following the schedule
    for step, (p, b) in enumerate(coord_schedule[:10]):
        w_proposal = [0, 0, 0, 0]
        success, error = runtime.step(w_proposal, budgets, B_norms_Q, eps_t, K_t)
        assert success

    # Verify audit bundle
    audit = create_audit_bundle(state, bg, schedule)
    assert audit["schedule_verification"]["valid"]
    assert audit["schedule_verification"]["period"] == 768


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
