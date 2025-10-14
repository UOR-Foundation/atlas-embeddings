from __future__ import annotations

from dataclasses import dataclass
from typing import List, Optional, Sequence, Tuple


# ---------------------------
# Data classes
# ---------------------------


@dataclass(frozen=True)
class Budgets:
    """Integer ACE budgets.

    Attributes
    ----------
    b, a: Lists of non-negative integers with the same length as the weight
        vector.  They encode the coefficients that scale the |w_i| terms for
        the two budget constraints.
    limit1_Q, limit2_Q: Integer limits in the same scale as ``w_i``.  The
        constraints are ``sum_i b_i |w_i| <= limit1_Q`` and
        ``sum_i a_i |w_i| <= limit2_Q``.
    Q: Global scaling constant used throughout the AEP stack.
    """

    b: Sequence[int]
    a: Sequence[int]
    limit1_Q: int
    limit2_Q: int
    Q: int


@dataclass(frozen=True)
class ProjResult:
    """Result of the integer projection."""

    w_star_Q: List[int]
    sum1: int
    sum2: int
    lam_Q: int
    mu_Q: int


@dataclass(frozen=True)
class AceMetrics:
    """Convenience structure used by the SPASC and PI runtimes."""

    slope_scaled: int
    gap_scaled: int
    sum_abs_w_Q: int
    sum_norms_Q: int
    rho_hat_scaled_opt: Optional[int] = None


# ---------------------------
# Helpers
# ---------------------------


def _weighted_l1(weights: Sequence[int], coeffs: Sequence[int]) -> int:
    total = 0
    for w, c in zip(weights, coeffs):
        total += abs(int(c)) * abs(int(w))
    return total


def _min_fraction(
    current: Tuple[int, int],
    candidate: Tuple[int, int],
) -> Tuple[int, int]:
    """Return the smaller fraction when both are positive.

    Fractions are encoded as ``(num, den)`` with ``den > 0``.  The comparison is
    done without introducing floating point arithmetic.
    """

    cur_num, cur_den = current
    cand_num, cand_den = candidate
    if cand_den <= 0:
        return current
    if cur_den <= 0:
        return candidate
    if cand_num * cur_den < cur_num * cand_den:
        return candidate
    return current


# ---------------------------
# Projection
# ---------------------------


def project_dual_int(wtilde_Q: Sequence[int], budgets: Budgets) -> ProjResult:
    """Project ``wtilde`` to satisfy both weighted L1 budgets.

    The projection uses a simple radial scaling that keeps the direction of
    ``wtilde`` while shrinking it just enough to respect the limits.  The method
    is deterministic and uses only integer arithmetic.
    """

    w_vec = [int(v) for v in wtilde_Q]
    b = [int(x) for x in budgets.b]
    a = [int(x) for x in budgets.a]

    if len(b) < len(w_vec):
        b = b + [0] * (len(w_vec) - len(b))
    if len(a) < len(w_vec):
        a = a + [0] * (len(w_vec) - len(a))

    total1 = _weighted_l1(w_vec, b)
    total2 = _weighted_l1(w_vec, a)

    scale = (1, 1)  # numerator, denominator
    if total1 > budgets.limit1_Q and total1 > 0:
        scale = _min_fraction(scale, (budgets.limit1_Q, total1))
    if total2 > budgets.limit2_Q and total2 > 0:
        scale = _min_fraction(scale, (budgets.limit2_Q, total2))

    num, den = scale
    if den <= 0:
        den = 1
    if num <= 0:
        num = 0

    if num < den:
        w_star = [(v * num) // den for v in w_vec]
    else:
        w_star = list(w_vec)

    sum1 = _weighted_l1(w_star, b)
    sum2 = _weighted_l1(w_star, a)
    lam_Q = max(total1 - budgets.limit1_Q, 0)
    mu_Q = max(total2 - budgets.limit2_Q, 0)
    return ProjResult(w_star_Q=w_star, sum1=sum1, sum2=sum2, lam_Q=lam_Q, mu_Q=mu_Q)


# ---------------------------
# Acceptance checks
# ---------------------------


def slope_bounds_scaled(
    w_star_Q: Sequence[int],
    B_norms_Q: Sequence[int],
    Q: int,
) -> Tuple[int, int, AceMetrics]:
    """Compute conservative slope bounds using integer arithmetic."""

    slope = 0
    sum_abs_w = 0
    sum_norms = 0
    for w, n in zip(w_star_Q, B_norms_Q):
        aw = abs(int(w))
        an = abs(int(n))
        slope += aw * an
        sum_abs_w += aw
        sum_norms += an
    gap = Q * Q - slope
    if gap < 0:
        gap = 0
    metrics = AceMetrics(
        slope_scaled=slope,
        gap_scaled=gap,
        sum_abs_w_Q=sum_abs_w,
        sum_norms_Q=sum_norms,
        rho_hat_scaled_opt=None,
    )
    return slope, gap, metrics


def ace_accept(
    w_star_Q: Sequence[int],
    B_norms_Q: Sequence[int],
    Q: int,
    rho_hat_scaled_opt: Optional[int],
) -> Tuple[bool, AceMetrics]:
    """Return ``(accepted, metrics)`` for the projected weights."""

    slope, gap, metrics = slope_bounds_scaled(w_star_Q, B_norms_Q, Q)
    sum_abs = metrics.sum_abs_w_Q
    if sum_abs == 0:
        ok = True
    else:
        ok = slope < Q * sum_abs
    if rho_hat_scaled_opt is not None:
        ok = ok and slope <= int(rho_hat_scaled_opt)
    metrics = AceMetrics(
        slope_scaled=metrics.slope_scaled,
        gap_scaled=metrics.gap_scaled,
        sum_abs_w_Q=metrics.sum_abs_w_Q,
        sum_norms_Q=metrics.sum_norms_Q,
        rho_hat_scaled_opt=rho_hat_scaled_opt,
    )
    return ok, metrics


__all__ = [
    "AceMetrics",
    "Budgets",
    "ProjResult",
    "ace_accept",
    "project_dual_int",
    "slope_bounds_scaled",
]

