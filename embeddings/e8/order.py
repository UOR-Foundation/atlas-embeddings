from __future__ import annotations

from typing import Tuple
from fractions import Fraction as Q

from core.arithmetic import Q as _Q

Vector = Tuple[Q, ...]
# height vector is fixed and public; ensures deterministic tie-breaks
HEIGHT = tuple(_Q(i + 1) for i in range(8))  # (1,2,3,4,5,6,7,8)


def frac_key(x: Q):
    # Fraction already normalized; denominator > 0
    return (x.numerator, x.denominator)


def dot(v: Vector, w: Vector) -> Q:
    return sum(v[i] * w[i] for i in range(8))


def iota_key(v: Vector):
    # stable, architecture-independent key
    n2 = dot(v, v)  # = 2 for E8 roots, kept for generality
    h = dot(v, HEIGHT)  # separates many ties
    return (
        frac_key(n2),
        frac_key(h),
        tuple(frac_key(c) for c in v),  # final lexicographic fallback
    )
