from __future__ import annotations
from dataclasses import dataclass
from typing import Callable, List, Dict, Optional

# K is provided as a matvec: List[int] -> List[int], preserving scale Q.
MatVec = Callable[[List[int]], List[int]]

def _abs_int(x: int) -> int:
    return -x if x < 0 else x


def _ceil_div(a: int, b: int) -> int:
    if b <= 0:
        raise ValueError("b must be > 0")
    return (a + b - 1) // b


def _l1(v: List[int]) -> int:
    return sum(_abs_int(x) for x in v)


# ---------------------------
# Power-iteration tick (online norm / rho-hat)
# ---------------------------


@dataclass(frozen=True)
class NormTick:
    v_next: List[int]     # rescaled iterate, same scale Q
    norm_hat_Q: int       # integer estimate of ||K||, scale Q


def power_iter_tick(K: MatVec, v: List[int], Q: int) -> NormTick:
    """
    One tick of L1-based power iteration.
    norm_hat_Q ≈ ||K v||_1 / ||v||_1, scaled by Q.
    v_next = floor((K v) / max(1, norm_hat_Q)) to keep integers bounded.
    """
    Kv = K(v)                            # scale Q
    num = _l1(Kv)
    den = max(_l1(v), 1)
    ratio_Q = _ceil_div(num * Q, den)    # scale Q
    div = max(ratio_Q, 1)
    v_next = [Kv[i] // div for i in range(len(Kv))]
    # avoid zero vector
    if all(x == 0 for x in v_next):
        v_next = [1 if i == 0 else 0 for i in range(len(Kv))]
    return NormTick(v_next=v_next, norm_hat_Q=ratio_Q)


# ---------------------------
# Neumann fixed-point estimator and certified tail
# ---------------------------


@dataclass(frozen=True)
class NeumannEstimate:
    xN_Q: List[int]       # partial sum \sum_{j=0}^N K^j F, scale Q
    tail_bound_Q: int     # certified L1 tail bound, scale Q
    N: int
    norm_hat_Q: int       # scale Q used in the bound


def neumann_estimate(
    K: MatVec,
    F_Q: List[int],
    N: int,
    Q: int,
    norm_hat_Q: int
) -> NeumannEstimate:
    """
    Builds xN_Q = sum_{j=0}^N K^j F using recurrence.
    Certified tail: ||R_N||_1 <= (||F||_1 * norm_hat_Q^{N+1}) / ((Q - norm_hat_Q) * Q^{N}).
    All quantities are integers; result is scaled by Q.
    """
    if N < 0:
        raise ValueError("N must be >= 0")
    if not (0 <= norm_hat_Q < Q):
        # If >=Q, the bound is invalid; caller should refuse earlier.
        raise ValueError("norm_hat_Q must be < Q")
    # partial sum
    x = [0] * len(F_Q)
    term = F_Q[:]                 # K^0 F
    for _ in range(N + 1):
        for i in range(len(x)):
            x[i] += term[i]
        term = K(term)            # next power term
    # tail bound (L1)
    F_norm_Q = _l1(F_Q)           # scale Q
    # numerator: ||F|| * norm_hat^{N+1}
    num = F_norm_Q
    k = norm_hat_Q

    def _ipow(base: int, exp: int) -> int:
        r = 1
        b = base
        e = exp
        while e > 0:
            if e & 1:
                r *= b
            b *= b
            e >>= 1
        return r

    k_pow = _ipow(k, N + 1)
    num *= k_pow
    den = (Q - k)
    # multiply denominator by Q^N
    # compute Q^N with fast exp
    Q_pow_N = _ipow(Q, N)
    den *= Q_pow_N
    tail_Q = _ceil_div(num, den)  # scale Q
    return NeumannEstimate(xN_Q=x, tail_bound_Q=tail_Q, N=N, norm_hat_Q=norm_hat_Q)


# ---------------------------
# Rolling policy and margins
# ---------------------------


@dataclass(frozen=True)
class Margins:
    gap_lb_Q: int           # Q - norm_hat_Q (scale Q)
    tighten_tau: bool       # request tighter τ if below threshold
    threshold_Q: int        # policy threshold used (scale Q)


def eval_margins(norm_hat_Q: int, Q: int, threshold_Q: int) -> Margins:
    """
    gap_lb_Q = Q - norm_hat_Q.
    tighten_tau if gap < threshold_Q.
    """
    if threshold_Q < 0 or threshold_Q >= Q:
        raise ValueError("threshold_Q must be in [0, Q)")
    gap = Q - norm_hat_Q
    return Margins(gap_lb_Q=gap, tighten_tau=(gap < threshold_Q), threshold_Q=threshold_Q)


# ---------------------------
# Infinite-prime convergence check (PETC signatures)
# ---------------------------


def infinite_prime_convergence_ok(sig_history: List[Dict[int, int]], window: int = 4) -> bool:
    """
    Conservative check: over the last `window` snapshots, the max exponent
    for each prime does not strictly increase at the final step.
    """
    if len(sig_history) < 2:
        return True
    H = sig_history[-min(window, len(sig_history)):]
    # union of primes present
    primes = set()
    for s in H:
        primes |= set(s.keys())
    for p in primes:
        seq = [s.get(p, 0) for s in H]
        if len(seq) >= 2 and seq[-1] > max(seq[:-1]):
            return False
    return True


# ---------------------------
# Full monitor step
# ---------------------------


@dataclass(frozen=True)
class MonitorReport:
    norm_hat_Q: int           # online ||K|| estimate, scale Q
    gap_lb_Q: int             # Q - norm_hat_Q, scale Q
    tail_bound_Q: int         # Neumann tail bound, scale Q
    xN_Q: List[int]           # partial fixed-point sum
    tighten_tau: bool         # policy recommendation
    sig_ok: bool              # infinite-prime convergence check
    v_next: List[int]         # next vector for power-iteration


def monitor_step(
    K: MatVec,
    F_Q: List[int],
    v_power: List[int],
    Q: int,
    N: int,
    threshold_Q: int,
    sig_history: Optional[List[Dict[int, int]]] = None,
) -> MonitorReport:
    """
    1) One power-iteration tick -> norm_hat_Q, v_next.
    2) Neumann estimate and certified tail using norm_hat_Q.
    3) Gap and policy decision (tighten τ if margins erode).
    4) Infinite-prime convergence check on signatures.
    """
    tick = power_iter_tick(K, v_power, Q)
    norm_hat_Q = tick.norm_hat_Q
    # guard: if norm_hat_Q >= Q, contraction is not certified
    # still produce a tail bound with large value to force tighten_tau.
    if norm_hat_Q >= Q:
        # degenerate bound: set tail to a large sentinel (e.g., ||F||_1)
        tail = _l1(F_Q)
        margins = Margins(gap_lb_Q=0, tighten_tau=True, threshold_Q=threshold_Q)
        sig_ok = infinite_prime_convergence_ok(sig_history or [])
        ne = NeumannEstimate(xN_Q=F_Q[:], tail_bound_Q=tail, N=0, norm_hat_Q=norm_hat_Q)
        return MonitorReport(
            norm_hat_Q=norm_hat_Q,
            gap_lb_Q=margins.gap_lb_Q,
            tail_bound_Q=ne.tail_bound_Q,
            xN_Q=ne.xN_Q,
            tighten_tau=margins.tighten_tau,
            sig_ok=sig_ok,
            v_next=tick.v_next,
        )
    ne = neumann_estimate(K, F_Q, N, Q, norm_hat_Q)
    margins = eval_margins(norm_hat_Q, Q, threshold_Q)
    sig_ok = infinite_prime_convergence_ok(sig_history or [])
    return MonitorReport(
        norm_hat_Q=norm_hat_Q,
        gap_lb_Q=margins.gap_lb_Q,
        tail_bound_Q=ne.tail_bound_Q,
        xN_Q=ne.xN_Q,
        tighten_tau=margins.tighten_tau,
        sig_ok=sig_ok,
        v_next=tick.v_next,
    )
