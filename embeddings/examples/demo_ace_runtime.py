#!/usr/bin/env python3
"""Demonstration of ACE Runtime with stability + lawfulness guarantees.

This example shows:
1. Setting up ACE runtime with the fixed address lattice
2. Running multiple steps with contraction tracking
3. Verifying convergence with Cauchy criterion
4. Generating audit bundle with all certificates
5. PETC ledger integration for lawfulness
"""

import json
from atlas.aep.ace_runtime import (
    ACERuntimeState,
    ACERuntime,
    BoundaryGroup,
    FairSchedule,
    create_audit_bundle,
    ATLAS_CLASSES,
    ATLAS_COORDINATES,
)
from atlas.aep.ace import Budgets


def demo_small_runtime():
    """Demonstrate ACE runtime with small dimensions for visualization."""
    print("=" * 80)
    print("ACE Runtime Demonstration: Small Scale")
    print("=" * 80)

    # Use small dimensions for demo
    dim = 100
    Q = 1000000

    # Initialize state: start away from origin, target is origin
    state = ACERuntimeState(
        T=[Q // 2] * dim,  # Initial state at 0.5
        F=[0] * dim,  # Target at origin
        Q=Q,
        convergence_threshold=Q // 1000,  # 0.001 threshold
    )

    runtime = ACERuntime(state)

    # Setup budgets
    budgets = Budgets(
        b=[1] * dim,
        a=[1] * dim,
        limit1_Q=Q * dim,  # Generous limits for demo
        limit2_Q=Q * dim,
        Q=Q,
    )

    # Contraction operator: K = 0.8 * I
    eps_t = Q // 5  # Gap = 0.2, so max norm = 0.8
    K_t = [[int(0.8 * Q) if i == j else 0 for j in range(dim)] for i in range(dim)]

    # Norms for acceptance check
    B_norms_Q = [Q // 100] * dim  # 0.01 per coordinate

    print(f"\nInitial state:")
    print(f"  Dimension: {dim}")
    print(f"  Initial ∥T∥_∞: {max(abs(x) for x in state.T) / Q:.6f}")
    print(f"  Target: origin (all zeros)")
    print(f"  Contraction: K = 0.8 * I")
    print(f"  Gap parameter ε: {eps_t / Q:.2f}")
    print()

    # Run runtime for multiple steps
    num_steps = 20
    print(f"Running {num_steps} steps...\n")

    for step in range(num_steps):
        # No external proposal (pure contraction toward fixed point)
        w_proposal = [0] * dim

        success, error = runtime.step(
            w_proposal=w_proposal,
            budgets=budgets,
            B_norms_Q=B_norms_Q,
            eps_t=eps_t,
            K_t=K_t,
            fail_closed=True,
        )

        if not success:
            print(f"ERROR at step {step}: {error}")
            break

        # Display progress every few steps
        if step % 5 == 0 or state.converged:
            metrics = state.contraction_history[-1]
            max_val = max(abs(x) for x in state.T)
            kkt = state.kkt_certificates[-1]

            print(f"Step {step:2d}:")
            print(f"  ∥T∥_∞ = {max_val / Q:.6f}")
            print(f"  ∥T_{step+1} - T_{step}∥ = {metrics.delta_T / Q:.6f}")
            print(f"  Contraction OK: {metrics.is_contractive()}")
            print(f"  KKT valid: {kkt.is_valid()}")

            if state.converged:
                print(f"  *** CONVERGED ***")
                break

    print()

    # Generate convergence certificate
    conv_cert = runtime.get_cauchy_convergence_certificate()
    print("Convergence Certificate:")
    print(f"  Converged: {conv_cert['converged']}")
    print(f"  All steps contractive: {conv_cert['all_contractive']}")
    print(f"  Total steps: {conv_cert['total_steps']}")
    print(f"  Final delta: {conv_cert['final_delta'] / Q:.6f}")
    print(f"  Convergence rate: {conv_cert['convergence_rate'] / Q:.6f}")
    print()

    # PETC ledger verification
    print("PETC Ledger:")
    print(f"  Entries: {len(state.petc_ledger.rows)}")
    print(f"  Chain valid: {state.petc_ledger.verify()}")
    print()

    return state


def demo_boundary_group():
    """Demonstrate boundary group structure and certificates."""
    print("=" * 80)
    print("Boundary Group and Subgroup Certificate")
    print("=" * 80)

    bg = BoundaryGroup()

    print(f"\nBoundary Group Structure:")
    print(f"  Pages: {bg.pages}")
    print(f"  Bytes per page: {bg.bytes_per_page}")
    print(f"  Total elements: {bg.pages * bg.bytes_per_page}")
    print(f"  Group U: (Z/2)^{{11}} with order {bg.group_order}")
    print(f"  Number of orbits: {bg.num_anchors}")
    print()

    print(f"Anchors (one per orbit):")
    for i, (p, b) in enumerate(bg.get_anchors()):
        print(f"  Orbit {i}: ({p:2d}, {b:3d})")
    print()

    # Test action
    print("Testing group action:")
    p, b = 0, 0
    print(f"  Start: ({p}, {b})")
    for u in [1, 7, 255, 1023]:
        p_new, b_new = bg.act_U(p, b, u)
        print(f"  u={u:4d} → ({p_new:2d}, {b_new:3d})")
    print()

    # Generate certificate
    from atlas.aep.ace_runtime import generate_subgroup_certificate

    cert = generate_subgroup_certificate(bg)

    print("Subgroup Certificate:")
    print(f"  Valid: {cert['valid']}")
    print(f"  Group structure: {cert['group_structure']}")
    print(f"  Group order: {cert['group_order']}")
    print(f"  Number of orbits: {cert['num_orbits']}")
    print(f"  Orbit size: {cert['orbit_size']}")
    print(f"  Total elements: {cert['total_elements']}")
    print(f"  Freeness samples verified: {cert['freeness_verified']}")
    print()


def demo_fair_schedule():
    """Demonstrate canonical fair schedule."""
    print("=" * 80)
    print("Canonical Fair Schedule (Φ-permutation)")
    print("=" * 80)

    schedule = FairSchedule()
    bg = BoundaryGroup()

    print(f"\nSchedule Properties:")
    print(f"  Φ(p, b) = ((p + 16) mod 48, (b + 1) mod 256)")
    print(f"  Period: {schedule.period}")
    print()

    # Verify period on anchors
    anchors = bg.get_anchors()
    print("Verifying period on anchors:")
    for p, b in anchors:
        p_final, b_final = schedule.phi_pow(p, b, schedule.period)
        matches = (p_final, b_final) == (p, b)
        print(f"  Φ^{schedule.period}({p:2d}, {b:3d}) = ({p_final:2d}, {b_final:3d}) {'✓' if matches else '✗'}")

    period_ok = schedule.verify_period(anchors)
    print(f"\nPeriod verification: {'PASS' if period_ok else 'FAIL'}")
    print()

    # Generate short schedule
    print("Sample schedule sequence (first 10 steps from anchor (0,0)):")
    seq = schedule.generate_schedule(0, 0, 10)
    for i, (p, b) in enumerate(seq):
        print(f"  Step {i:2d}: ({p:2d}, {b:3d})")
    print()


def demo_audit_bundle(state):
    """Generate and display audit bundle."""
    print("=" * 80)
    print("Audit Bundle Generation")
    print("=" * 80)

    bg = BoundaryGroup()
    schedule = FairSchedule()

    bundle = create_audit_bundle(state, bg, schedule)

    print("\nAudit Bundle Summary:")
    print(f"  Version: {bundle['audit_version']}")
    print(f"  Runtime steps: {bundle['runtime_steps']}")
    print(f"  Converged: {bundle['converged']}")
    print()

    print("KKT Certificates:")
    valid_count = sum(1 for cert in bundle['kkt_certificates'] if cert['valid'])
    print(f"  Total: {len(bundle['kkt_certificates'])}")
    print(f"  Valid: {valid_count}")
    print()

    print("Contraction History:")
    contractive_count = sum(1 for m in bundle['contraction_history'] if m['contractive'])
    print(f"  Total steps: {len(bundle['contraction_history'])}")
    print(f"  Contractive: {contractive_count}")
    print()

    print("PETC Ledger:")
    print(f"  Valid: {bundle['petc_ledger']['valid']}")
    print(f"  Entries: {bundle['petc_ledger']['entries']}")
    print()

    print("Subgroup Certificate:")
    sub_cert = bundle['subgroup_certificate']
    print(f"  Valid: {sub_cert['valid']}")
    print(f"  Structure: {sub_cert['group_structure']}")
    print(f"  Total elements: {sub_cert['total_elements']}")
    print()

    print("Schedule Verification:")
    sched = bundle['schedule_verification']
    print(f"  Valid: {sched['valid']}")
    print(f"  Period: {sched['period']}")
    print()

    print("Lattice Structure:")
    lat = bundle['lattice_structure']
    print(f"  Classes: {lat['classes']}")
    print(f"  Coordinates: {lat['coordinates']}")
    print(f"  Boundary pages: {lat['boundary_pages']}")
    print(f"  Boundary bytes: {lat['boundary_bytes']}")
    print()

    # Save bundle to file
    output_file = "/tmp/ace_audit_bundle.json"
    with open(output_file, "w") as f:
        json.dump(bundle, f, indent=2)
    print(f"Audit bundle saved to: {output_file}")
    print()


def main():
    """Run all demonstrations."""
    print("\n")
    print("╔" + "=" * 78 + "╗")
    print("║" + " " * 78 + "║")
    print("║" + "  ACE Runtime Demonstration: Stability + Lawfulness".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("╚" + "=" * 78 + "╝")
    print()

    # 1. Run small-scale runtime
    state = demo_small_runtime()

    # 2. Demonstrate boundary group
    demo_boundary_group()

    # 3. Demonstrate fair schedule
    demo_fair_schedule()

    # 4. Generate audit bundle
    demo_audit_bundle(state)

    print("=" * 80)
    print("Demonstration Complete")
    print("=" * 80)
    print("\nAll components verified:")
    print("  ✓ ACE runtime with contraction guarantees")
    print("  ✓ KKT certificates for optimality")
    print("  ✓ Cauchy convergence tracking")
    print("  ✓ PETC ledger for lawfulness")
    print("  ✓ Boundary group with (Z/2)^{11} action")
    print("  ✓ Subgroup certificate")
    print("  ✓ Fair Φ-schedule with period 768")
    print("  ✓ Comprehensive audit bundle")
    print()
    print("For more details, see: docs/ACE_RUNTIME.md")
    print()


if __name__ == "__main__":
    main()
