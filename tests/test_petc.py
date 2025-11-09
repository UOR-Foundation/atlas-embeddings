from atlas.aep.petc import (
    axis_signature, tensor_signature, add_signatures, eq_signatures,
    cert_tensor_product, cert_contraction,
    ChannelRow, PETCLedger,
    pack_rb, unpack_rb, act_U, anchors_S,
    Phi, phi_pow,
    verify_freeness_sample, verify_orbit_counts, verify_C768_closure,
)
from petc.phi import verify_phi_equivariance_sample


# ---- signature and certificates ----


def test_axis_and_tensor_signature():
    # 12 = 2^2 * 3
    s12 = axis_signature(12)
    assert s12.get(2, 0) == 2 and s12.get(3, 0) == 1
    # 20 = 2^2 * 5
    s20 = axis_signature(20)
    # tensor with axes [12,20] has exponents sum
    tall = tensor_signature([12, 20])
    assert tall.get(2, 0) == 4 and tall.get(3, 0) == 1 and tall.get(5, 0) == 1
    # product cert
    assert cert_tensor_product(s12, s20, add_signatures(s12, s20))


def test_contraction_certificate():
    # A: [12,7], B: [49,12]; contract A[0] with B[1] (both 12)
    axesA = [12, 7]
    axesB = [49, 12]
    assert cert_contraction(axesA, axesB, [(0, 1)]) is True
    # mismatch example: 7 vs 8
    axesB2 = [49, 8]
    assert cert_contraction(axesA, axesB2, [(1, 1)]) is False


# ---- ledger ----


def test_ledger_and_budgets():
    L = PETCLedger()
    L.add_channel(ChannelRow(id="c1", sigma=axis_signature(12), budget=5, commutator_class="X"))
    L.add_channel(ChannelRow(id="c2", sigma=axis_signature(20), budget=3, commutator_class="X"))
    assert L.get_budget("X") == 5  # initialized from first row
    rem = L.decrement_commutator("X", 2)
    assert rem == 3
    rem = L.decrement_commutator("X", 3)
    assert rem == 0
    try:
        L.decrement_commutator("X", 1)
        assert False, "expected breach"
    except RuntimeError:
        pass


# ---- group gate ----


def test_pack_unpack_and_action():
    # round-trip
    for p in (0, 7, 8, 15, 16, 23, 24, 31, 32, 39, 40, 47):
        for b in (0, 1, 2, 255):
            r, idx = pack_rb(p, b)
            p2, b2 = unpack_rb(r, idx)
            assert (p, b) == (p2, b2)
    # anchors
    S = anchors_S()
    assert S == [(0, 0), (8, 0), (16, 0), (24, 0), (32, 0), (40, 0)]
    # free action samples and orbit counts
    assert verify_freeness_sample()
    assert verify_orbit_counts()


def test_phi_schedule_and_equivariance():
    # order 768 closure on anchors
    assert verify_C768_closure()
    # sample equivariance Φ(act_U)=act_U(Φ)
    G = [(8 * k, 0) for k in range(6)]
    U = [(0,) * 11, (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)]

    def bits_to_int(bits: tuple[int, ...]) -> int:
        total = 0
        for idx, bit in enumerate(bits):
            if bit:
                total |= 1 << idx
        return total

    def phi_pair(g: tuple[int, int]) -> tuple[int, int]:
        return Phi(g[0], g[1])

    def act_U_on_G(u: tuple[int, ...], g: tuple[int, int]) -> tuple[int, int]:
        return act_U(g[0], g[1], bits_to_int(u))

    assert verify_phi_equivariance_sample(
        G,
        U,
        phi_pair,
        act_U_on_G,
        act_U_on_G,
        debug=True,
    )


def test_phi_pow():
    # k=768 -> identity
    for p, b in anchors_S():
        p2, b2 = phi_pow(p, b, 768)
        assert (p, b) == (p2, b2)
    # k=1 -> matches Phi
    for p, b in ((0, 0), (7, 255), (31, 42)):
        assert Phi(p, b) == phi_pow(p, b, 1)
