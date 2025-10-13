from __future__ import annotations

from fractions import Fraction as Q
from typing import Dict, List, Tuple

from e8.roots import dot

Vector = Tuple[Q, ...]


def multiset_counts(vecs: List[Vector]) -> Dict[int, int]:
    n = len(vecs)
    out = {-2: 0, -1: 0, 0: 0, 1: 0}
    for i in range(n):
        vi = vecs[i]
        for j in range(i + 1, n):
            vj = vecs[j]
            ip = dot(vi, vj)
            if ip not in {Q(-2), Q(-1), Q(0), Q(1)}:
                raise ValueError(f"unexpected inner product {ip}")
            out[int(ip)] += 1
    return out
