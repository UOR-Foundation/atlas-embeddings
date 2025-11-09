from typing import List

from atlas.aep.ace import Budgets
from atlas.aep.spasc import (
    SpascConfig,
    SpascState,
    spasc_step,
    spasc_train,
)


def _quad_grad(Q: int):
    def g(w_Q: List[int], t: int) -> List[int]:
        return [int(x) for x in w_Q]

    return g


def test_spasc_single_step_projection_and_accept():
    Q = 10**6
    w0 = [2 * Q, Q, 0]
    b = [1, 1, 1]
    a = [1, 1, 1]
    budgets = Budgets(b=b, a=a, limit1_Q=1 * Q, limit2_Q=1 * Q, Q=Q)
    Bnorms = [Q // 4, Q // 4, Q // 4]
    cfg = SpascConfig(Q=Q, eta_Q=Q // 2, budgets=budgets, B_norms_Q=Bnorms, seed=123)
    state = SpascState(step=0, w_Q=w0)

    next_state, log = spasc_step(state, cfg, _quad_grad(Q))

    assert log.accepted
    assert log.proj.sum1 <= budgets.limit1_Q
    assert log.proj.sum2 <= budgets.limit2_Q
    assert log.slope_scaled < Q * Q
    assert next_state.step == 1


def test_spasc_train_converges_and_logs():
    Q = 10**6
    w0 = [Q, Q]
    b = [1, 1]
    a = [1, 1]
    budgets = Budgets(b=b, a=a, limit1_Q=1 * Q, limit2_Q=1 * Q, Q=Q)
    Bnorms = [Q // 3, Q // 3]
    cfg = SpascConfig(Q=Q, eta_Q=Q // 4, budgets=budgets, B_norms_Q=Bnorms, seed=7)

    res = spasc_train(w0, cfg, _quad_grad(Q), max_steps=5, stop_on_fault=True)

    assert res.logs[0].accepted
    assert res.pass_all

    def l1(v: List[int]) -> int:
        return sum(abs(x) for x in v)

    assert l1(res.final.w_Q) <= l1(w0)


def test_spasc_fault_on_violation():
    Q = 10**6
    w0 = [Q, Q]
    b = [1, 1]
    a = [1, 1]
    budgets = Budgets(b=b, a=a, limit1_Q=Q // 2, limit2_Q=Q // 2, Q=Q)
    Bnorms = [Q, Q]
    cfg = SpascConfig(Q=Q, eta_Q=Q // 10, budgets=budgets, B_norms_Q=Bnorms, seed=0)

    res = spasc_train(w0, cfg, _quad_grad(Q), max_steps=3, stop_on_fault=True)

    assert not res.pass_all
    assert len(res.logs) >= 1
    assert res.logs[-1].accepted in (True, False)

