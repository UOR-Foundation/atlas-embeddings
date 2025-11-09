from atlas.aep.moonshine import (
    OperatorDef,
    MoonshineConfig,
    check_typing,
    small_gain_accept,
    accept_feedback_interconnection,
)
from atlas.aep.petc import PETCLedger, ChannelRow


def _ops(Q: int):
    G1 = OperatorDef(
        id="G1",
        in_sig={2: 1},
        out_sig={3: 2},
        norm_Q=Q // 3,
        commutator_class="X",
    )
    G2 = OperatorDef(
        id="G2",
        in_sig={3: 2},
        out_sig={2: 1},
        norm_Q=Q // 4,
        commutator_class="Y",
    )
    return G1, G2


def test_typing_and_small_gain():
    Q = 10**6
    G1, G2 = _ops(Q)
    assert check_typing(G1, G2)
    sg = small_gain_accept(G1.norm_Q, G2.norm_Q, Q)
    assert sg.ok and sg.product_scaled < Q * Q


def test_accept_feedback_and_zk_sketch():
    Q = 10**6
    G1, G2 = _ops(Q)
    cfg = MoonshineConfig(Q=Q)
    ledger = PETCLedger()
    ledger.add_channel(
        ChannelRow(id="cX", sigma={2: 1}, budget=2, commutator_class="X")
    )
    ledger.add_channel(
        ChannelRow(id="cY", sigma={3: 1}, budget=1, commutator_class="Y")
    )
    ace_metrics = [
        {"slope_scaled": Q * Q // 4, "gap_scaled": Q * Q - (Q * Q // 4), "Q2": Q * Q}
    ]
    acc, sketch, remaining = accept_feedback_interconnection(
        G1,
        G2,
        cfg,
        ledger,
        ace_metrics,
        seed_hex="ab",
    )
    assert acc.typed_ok and acc.small_gain.ok and not acc.quarantine
    assert "c1" in sketch.checks and "c2" in sketch.checks and sketch.challenge_hex
    assert remaining["X"] == 1 and remaining["Y"] == 0


def test_reject_on_budget_and_typing():
    Q = 10**6
    G1 = OperatorDef(
        id="G1",
        in_sig={2: 1},
        out_sig={5: 1},
        norm_Q=Q // 2,
        commutator_class="X",
    )
    G2 = OperatorDef(
        id="G2",
        in_sig={3: 1},
        out_sig={2: 1},
        norm_Q=Q // 2,
        commutator_class="X",
    )
    cfg = MoonshineConfig(Q=Q)
    ledger = PETCLedger()
    ledger.add_channel(
        ChannelRow(id="c", sigma={2: 1}, budget=0, commutator_class="X")
    )
    ace_metrics = [
        {"slope_scaled": Q // 2, "gap_scaled": Q * Q - Q // 2, "Q2": Q * Q}
    ]
    acc, _, _ = accept_feedback_interconnection(
        G1,
        G2,
        cfg,
        ledger,
        ace_metrics,
        seed_hex="cd",
    )
    assert not acc.typed_ok
    assert acc.quarantine
