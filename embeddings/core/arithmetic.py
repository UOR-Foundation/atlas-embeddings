from __future__ import annotations

from fractions import Fraction as Q
from typing import Iterable, Tuple

# single source of truth for exact arithmetic
__all__ = ["Q", "is_Q", "as_Q", "tupleQ"]

def is_Q(x) -> bool:
    return isinstance(x, Q)


def as_Q(x) -> Q:
    if isinstance(x, Q):
        return x
    if isinstance(x, int):
        return Q(x)
    if isinstance(x, str):
        return Q(x)  # "1/2" safe
    raise TypeError(f"non-rational input: {type(x)}")


def tupleQ(xs: Iterable) -> Tuple[Q, ...]:
    return tuple(as_Q(x) for x in xs)
