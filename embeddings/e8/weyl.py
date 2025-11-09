from __future__ import annotations

from fractions import Fraction as Q
from typing import List, Tuple

from .roots import Vector, dot

Matrix = List[List[Q]]


def reflect(r: Vector, v: Vector) -> Vector:
    """Reflect vector ``v`` across the root ``r``."""
    c = (2 * dot(v, r)) / Q(2)
    return tuple(v[i] - c * r[i] for i in range(8))


def mat_from_columns(cols: List[Vector]) -> Matrix:
    return [[cols[j][i] for j in range(8)] for i in range(8)]


def mat_mul(A: Matrix, v: Vector) -> Vector:
    return tuple(sum(A[i][j] * v[j] for j in range(8)) for i in range(8))


def mat_inv(A: Matrix) -> Matrix:
    n = 8
    M: List[List[Q]] = [
        [A[i][j] for j in range(n)] + [Q(int(i == j)) for j in range(n)] for i in range(n)
    ]
    for i in range(n):
        if M[i][i] == 0:
            for k in range(i + 1, n):
                if M[k][i] != 0:
                    M[i], M[k] = M[k], M[i]
                    break
        piv = M[i][i]
        if piv == 0:
            raise ValueError("singular matrix")
        for j in range(2 * n):
            M[i][j] /= piv
        for k in range(n):
            if k == i:
                continue
            f = M[k][i]
            if f == 0:
                continue
            for j in range(2 * n):
                M[k][j] -= f * M[i][j]
    return [row[n:] for row in M]


def mat_mul_mat(A: Matrix, B: Matrix) -> Matrix:
    n = 8
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
