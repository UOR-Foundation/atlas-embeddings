from __future__ import annotations

import math
from collections.abc import Sequence


def _to_vector(values: Sequence[float]) -> list[float]:
    return [float(v) for v in values]


def _vector_norm(vec: Sequence[float]) -> float:
    return math.sqrt(sum(float(v) ** 2 for v in vec))


def _matrix_norm(matrix: Sequence[Sequence[float]]) -> float:
    return math.sqrt(sum(float(v) ** 2 for row in matrix for v in row))


def _matvec(matrix: Sequence[Sequence[float]], vec: Sequence[float]) -> list[float]:
    vector = _to_vector(vec)
    return [sum(float(a) * float(b) for a, b in zip(row, vector)) for row in matrix]


def monitor_tick(state, K, F, x_t, gapLB, slopeUB, tailspec):
    K_vec = _matvec(K, x_t)
    x_next = [f + delta for f, delta in zip(_to_vector(F), K_vec)]
    normK = _matrix_norm(K)
    f_norm = _vector_norm(_to_vector(F))
    if normK < 1:
        tail = (normK ** (tailspec["N"] + 1)) / (1.0 - max(normK, 1e-16)) * f_norm
    else:
        tail = float("inf")
    status = {"gapLB": gapLB, "slopeUB": slopeUB, "normK": normK, "tail": tail}
    state = {"x": x_next, "status": status}
    return state
