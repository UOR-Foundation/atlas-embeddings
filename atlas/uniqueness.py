from __future__ import annotations

from fractions import Fraction as Q
from typing import Dict, List

from e8.roots import Vector
from e8.weyl import mat_from_columns, mat_inv, mat_mul, mat_mul_mat


def matrix_between_embeddings(S1: List[Vector], S2: List[Vector]) -> List[List[Q]]:
    A = mat_from_columns(S1)
    B = mat_from_columns(S2)
    Ainv = mat_inv(A)
    return mat_mul_mat(B, Ainv)


def permutes_root_set(M: List[List[Q]], roots: List[Vector]) -> bool:
    S = set(roots)
    for r in roots:
        if tuple(mat_mul(M, r)) not in S:
            return False
    return True
