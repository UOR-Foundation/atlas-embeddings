from typing import Dict, List

from atlas.aep.ace import Budgets
from atlas.aep.petc import ChannelRow, PETCLedger
from atlas.aep.pi_adapter import ChannelDef, PiAtom, PiConfig, pi_runtime_step


def _mv_scale_k(Q: int, k_num: int):
    # Bp(v) = (k_num/Q)*v, encoded as integer map: out_i = (k_num * v_i) // Q

    def mv(v: List[int]) -> List[int]:
        return [(k_num * x) // Q for x in v]

    return mv


def _channels(Q: int) -> Dict[str, ChannelDef]:
    # two channels with modest norms
    return {
        "c1": ChannelDef(
            id="c1",
            sigma={2: 1},
            commutator_class="X",
            B_norm_Q=Q // 2,
            B_matvec=_mv_scale_k(Q, Q // 2),
        ),
        "c2": ChannelDef(
            id="c2",
            sigma={3: 1},
            commutator_class="X",
            B_norm_Q=Q // 3,
            B_matvec=_mv_scale_k(Q, Q // 3),
        ),
    }


def test_pi_step_accepts_and_updates_ledger():
    Q = 10**6
    ch = _channels(Q)
    # budgets: sum b_i |w_i| <= 1*Q, sum a_i|w_i| <= 1*Q  (tight)
    b = [1, 1]
    a = [1, 1]
    budgets = Budgets(b=b, a=a, limit1_Q=1 * Q, limit2_Q=1 * Q, Q=Q)
    cfg = PiConfig(Q=Q, budgets=budgets, dim=3)
    # ledger with room for two uses of class X
    ledger = PETCLedger()
    ledger.add_channel(ChannelRow(id="c1", sigma=ch["c1"].sigma, budget=2, commutator_class="X"))
    # second row shares class; budget initialized from first row
    ledger.add_channel(ChannelRow(id="c2", sigma=ch["c2"].sigma, budget=2, commutator_class="X"))
    # atoms propose large weights; projection will shrink into budget
    atoms = [
        PiAtom(id="a1", channel_id="c1", wtilde_Q=2 * Q),
        PiAtom(id="a2", channel_id="c2", wtilde_Q=2 * Q),
    ]
    F = [0, 0, 0]
    T = [Q, 0, 0]
    step = pi_runtime_step(atoms, ch, cfg, ledger, F, T, rho_hat_scaled_opt=None)
    assert step.accepted
    # ledger decremented by number of used channels
    assert step.audit.petc_budgets["X"] == 0
    # nonzero weights present
    assert any(v != 0 for v in step.w_star_map_Q.values())


def test_pi_quarantine_on_budget_breach():
    Q = 10**6
    ch = _channels(Q)
    b = [1, 1]
    a = [1, 1]
    budgets = Budgets(b=b, a=a, limit1_Q=2 * Q, limit2_Q=2 * Q, Q=Q)
    cfg = PiConfig(Q=Q, budgets=budgets, dim=2)
    # ledger with zero budget triggers quarantine when any channel used
    ledger = PETCLedger()
    ledger.add_channel(ChannelRow(id="c1", sigma=ch["c1"].sigma, budget=0, commutator_class="X"))
    ledger.add_channel(ChannelRow(id="c2", sigma=ch["c2"].sigma, budget=0, commutator_class="X"))
    atoms = [PiAtom(id="a", channel_id="c1", wtilde_Q=Q)]
    F = [0, 0]
    T = [0, 0]
    step = pi_runtime_step(atoms, ch, cfg, ledger, F, T, rho_hat_scaled_opt=None)
    assert step.audit.quarantine
    assert not step.accepted
