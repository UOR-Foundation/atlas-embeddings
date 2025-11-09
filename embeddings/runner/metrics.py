from __future__ import annotations

import math
import random
from collections.abc import Sequence


def _to_matrix(A: Sequence[Sequence[float]]) -> list[list[float]]:
    return [[float(value) for value in row] for row in A]


def _vector(values: Sequence[float]) -> list[float]:
    return [float(v) for v in values]


def _vector_norm(vec: Sequence[float]) -> float:
    return math.sqrt(sum(float(v) ** 2 for v in vec))


def _matvec(A: Sequence[Sequence[float]], x: Sequence[float]) -> list[float]:
    matrix = _to_matrix(A)
    vec = _vector(x)
    return [sum(r_elt * v_elt for r_elt, v_elt in zip(row, vec)) for row in matrix]


def power_iter_2norm(A, iters: int = 20, seed: int = 0) -> float:
    matrix = _to_matrix(A)
    cols = len(matrix[0]) if matrix else 0
    rng = random.Random(seed)
    x = [rng.gauss(0.0, 1.0) for _ in range(cols)] or [1.0]
    norm = _vector_norm(x) or 1.0
    x = [value / norm for value in x]
    for _ in range(iters):
        x = _matvec(matrix, x)
        n = _vector_norm(x)
        if n == 0:
            return 0.0
        x = [value / n for value in x]
    return float(_vector_norm(_matvec(matrix, x)))


def gershgorin_rho_upper(A) -> float:
    matrix = _to_matrix(A)
    radii = []
    for i, row in enumerate(matrix):
        center = abs(row[i]) if i < len(row) else 0.0
        radius = sum(abs(v) for v in row) - (abs(row[i]) if i < len(row) else 0.0)
        radii.append(center + radius)
    return float(max(radii, default=0.0))


def spectral_bounds(K):
    rho_hat = max(gershgorin_rho_upper(K), power_iter_2norm(K))
    norm_hat = power_iter_2norm(K)
    return rho_hat, norm_hat


def neumann_tail_bound(normK, N, normF):
    if normK >= 1:
        return float("inf")
    return (normK ** (N + 1)) / (1.0 - normK) * normF
