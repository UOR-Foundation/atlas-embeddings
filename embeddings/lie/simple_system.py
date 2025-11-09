from __future__ import annotations

from fractions import Fraction as Q
from typing import Iterable, List

from core.resgraph import Vector, dot


def _generic_height(roots: List[Vector]) -> Vector:
    dim = len(roots[0])
    coeffs = [Q(i + 1) for i in range(len(roots))]
    h = [Q(0)] * dim
    for coeff, r in zip(coeffs, roots):
        for i in range(dim):
            h[i] += coeff * r[i]
    return tuple(h)


def extract_simple_system(roots: Iterable[Vector]) -> List[Vector]:
    root_list = sorted(set(roots))
    if not root_list:
        return []
    h = _generic_height(root_list)
    positives = [r for r in root_list if dot(r, h) > Q(0)]
    positives_set = set(positives)
    simple: List[Vector] = []
    dim = len(root_list[0])
    for alpha in sorted(positives):
        decomposable = False
        for beta in positives:
            gamma = tuple(alpha[i] - beta[i] for i in range(dim))
            if gamma in positives_set:
                decomposable = True
                break
        if not decomposable:
            simple.append(alpha)
    return simple
