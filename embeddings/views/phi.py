"""Utility predicates on inner products for residual graph construction."""

from fractions import Fraction as Q


def phi_minus1(t: Q) -> bool:
    return t == Q(-1)


def phi_plus1(t: Q) -> bool:
    return t == Q(1)
