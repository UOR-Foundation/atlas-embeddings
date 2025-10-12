from __future__ import annotations

from fractions import Fraction as Q
from typing import Iterable, List, Tuple, Set

Vector = Tuple[Q, ...]
RootSet = List[Vector]


def dot(x: Vector, y: Vector) -> Q:
    """Exact inner product of two E8 vectors."""
    if len(x) != len(y):
        raise ValueError("dimension mismatch")
    return sum(a * b for a, b in zip(x, y))


def generate_e8_roots() -> RootSet:
    """Generate the 240 roots of the E8 root system in deterministic order."""
    R: Set[Vector] = set()

    # 112 integer roots with two ±1 entries and the rest zero.
    for i in range(8):
        for j in range(i + 1, 8):
            for si in (-1, 1):
                for sj in (-1, 1):
                    v = [Q(0)] * 8
                    v[i] = Q(si)
                    v[j] = Q(sj)
                    R.add(tuple(v))

    # 128 half-integer roots with an even number of +1/2 entries.
    half = [Q(1, 2), Q(-1, 2)]

    def parity_plus(vec: List[Q]) -> int:
        return sum(1 for x in vec if x == Q(1, 2)) % 2

    def rec(k: int, cur: List[Q]) -> None:
        if k == 8:
            if parity_plus(cur) == 0:
                R.add(tuple(cur))
            return
        for h in half:
            cur.append(h)
            rec(k + 1, cur)
            cur.pop()

    rec(0, [])

    # Freeze in lexicographic order for determinism.
    return sorted(R)


def phi_neg_one(t: Q) -> bool:
    """Return whether an inner product equals −1."""
    return t == Q(-1)


def neighbors_phi_minus_one(R: RootSet) -> List[List[int]]:
    """Adjacency lists of roots joined by inner product −1."""
    n = len(R)
    adj: List[List[int]] = [[] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if dot(R[i], R[j]) == Q(-1):
                adj[i].append(j)
                adj[j].append(i)
    return [sorted(xs) for xs in adj]
