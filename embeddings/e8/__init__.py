"""Utilities related to the E8 root system."""

from .roots import generate_e8_roots, dot, neighbors_phi_minus_one
from .weyl import (
    reflect,
    mat_from_columns,
    mat_inv,
    mat_mul,
    mat_mul_mat,
)

__all__ = [
    "generate_e8_roots",
    "dot",
    "neighbors_phi_minus_one",
    "reflect",
    "mat_from_columns",
    "mat_inv",
    "mat_mul",
    "mat_mul_mat",
]
