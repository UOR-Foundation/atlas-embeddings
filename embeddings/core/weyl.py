from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Tuple

from .resgraph import Vector

Matrix = Tuple[Tuple[Q, ...], ...]


def matmul(A: Matrix, x: Vector) -> Vector:
    n = len(A)
    if len(x) != n:
        raise ValueError("matrix/vector dimension mismatch")
    out: list[Q] = []
    for i in range(n):
        if len(A[i]) != n:
            raise ValueError("matrix must be square")
        s: Q = Q(0)
        for j in range(n):
            s += A[i][j] * x[j]
        out.append(s)
    return tuple(out)


@dataclass(frozen=True)
class WeylAction:
    M: Matrix

    def apply(self, v: Vector) -> Vector:
        return matmul(self.M, v)
