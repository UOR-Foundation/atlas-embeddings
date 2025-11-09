from typing import List
from atlas.aep.pirtm import (
    power_iter_tick, neumann_estimate, monitor_step, infinite_prime_convergence_ok
)

def _mv_scale(Q: int, k_num: int):
    # K(v) = floor((k_num/Q)*v), elementwise
    def mv(v: List[int]) -> List[int]:
        return [(k_num * x) // Q for x in v]
    return mv

def test_power_iter_tick_contracting():
    Q = 10**6
    k = Q // 2  # 0.5
    K = _mv_scale(Q, k)
    v = [Q, 0, 0]
    tick = power_iter_tick(K, v, Q)
    assert 0 < tick.norm_hat_Q < Q
    # next vector should be nonzero
    assert any(x != 0 for x in tick.v_next)

def test_neumann_estimate_bounds():
    Q = 10**6
    k = Q // 2               # ||K|| = 0.5
    K = _mv_scale(Q, k)
    F = [Q]                  # ||F||_1 = Q
    N = 4
    ne = neumann_estimate(K, F, N, Q, k)
    # tail bound should shrink as N increases
    ne2 = neumann_estimate(K, F, N+1, Q, k)
    assert ne2.tail_bound_Q <= ne.tail_bound_Q

def test_monitor_step_policy_and_sigcheck():
    Q = 10**6
    k = Q // 3               # 0.333...
    K = _mv_scale(Q, k)
    F = [Q, 0]
    v = [Q, Q]
    # threshold at 0.1 => 0.1*Q
    threshold_Q = Q // 10
    # simple bounded signature history
    sig_hist = [
        {2: 3, 3: 1},
        {2: 3, 3: 1},
        {2: 3, 3: 1},
    ]
    rep = monitor_step(K, F, v, Q, N=3, threshold_Q=threshold_Q, sig_history=sig_hist)
    assert rep.norm_hat_Q < Q
    assert rep.gap_lb_Q == Q - rep.norm_hat_Q
    assert rep.sig_ok
    # if we push norm near Q, policy tightens
    k2 = Q - (Q // 100)      # 0.99
    K2 = _mv_scale(Q, k2)
    rep2 = monitor_step(K2, F, v, Q, N=1, threshold_Q=threshold_Q, sig_history=sig_hist)
    assert rep2.tighten_tau

def test_infinite_prime_convergence_ok():
    # last step increases a prime exponent -> False
    hist = [{2:1},{2:1,3:1},{2:2,3:1}]
    assert not infinite_prime_convergence_ok(hist, window=3)
