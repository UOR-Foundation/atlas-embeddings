from __future__ import annotations

from fractions import Fraction as Q


def qstr(x: Q) -> str:
    return f"{x.numerator}/{x.denominator}" if x.denominator != 1 else str(x.numerator)
