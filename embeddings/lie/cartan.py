from __future__ import annotations

from fractions import Fraction as Q
from typing import List

from core.resgraph import Vector, dot


def cartan_matrix(simple: List[Vector]) -> List[List[int]]:
    """Compute the Cartan matrix associated with ``simple`` roots."""
    n = len(simple)
    A: List[List[int]] = [[0] * n for _ in range(n)]
    norms = [dot(alpha, alpha) for alpha in simple]
    for j in range(n):
        for i in range(n):
            numerator = Q(2) * dot(simple[i], simple[j])
            denominator = norms[j]
            value = numerator / denominator
            if value.denominator != 1:
                raise ValueError("non-integral Cartan entry")
            A[i][j] = int(value)
    return A
