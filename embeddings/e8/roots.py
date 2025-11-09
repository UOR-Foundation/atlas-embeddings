from __future__ import annotations

from fractions import Fraction as Q
from typing import Iterable, List, Tuple, Set

from core.arithmetic import Q as _Q
from .order import iota_key

Vector = Tuple[Q, ...]
RootSet = List[Vector]


def dot(x: Vector, y: Vector) -> Q:
    return sum(a * b for a, b in zip(x, y))


def generate_e8_roots() -> RootSet:
    R: Set[Vector] = set()
    # 112 integer roots: two ±1's, rest 0
    for i in range(8):
        for j in range(i + 1, 8):
            for si in (-1, 1):
                for sj in (-1, 1):
                    v = [_Q(0)] * 8
                    v[i] = _Q(si)
                    v[j] = _Q(sj)
                    R.add(tuple(v))
    # 128 half-integer roots: (±1/2,...,±1/2) with even # of + signs
    halves = (_Q(1, 2), _Q(-1, 2))

    def even_plus(v: Iterable[Q]) -> bool:
        return sum(1 for x in v if x == _Q(1, 2)) % 2 == 0

    def rec(k: int, cur: List[Q]):
        if k == 8:
            if even_plus(cur):
                R.add(tuple(cur))
            return
        for h in halves:
            cur.append(h)
            rec(k + 1, cur)
            cur.pop()

    rec(0, [])
    # paste-stable total order ι
    return sorted(R, key=iota_key)


def phi_neg_one(t: Q) -> bool:
    return t == _Q(-1)


def neighbors_phi_minus_one(R: RootSet) -> List[List[int]]:
    n = len(R)
    adj: List[List[int]] = [[] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if dot(R[i], R[j]) == _Q(-1):
                adj[i].append(j)
                adj[j].append(i)
    return [sorted(xs) for xs in adj]
