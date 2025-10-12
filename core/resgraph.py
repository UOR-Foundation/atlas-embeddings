from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Callable, FrozenSet, Mapping, Set, Tuple

Vertex = str
Vector = Tuple[Q, ...]
Edge = Tuple[Vertex, Vertex]
Phi = Callable[[Q], bool]


def dot(x: Vector, y: Vector) -> Q:
    """Return the exact rational inner product of two vectors."""
    if len(x) != len(y):
        raise ValueError("dimension mismatch")
    s: Q = Q(0)
    for a, b in zip(x, y):
        s += a * b
    return s


def canon_edge(u: Vertex, v: Vertex) -> Edge:
    """Return the canonical ordering of an undirected edge."""
    return (u, v) if u < v else (v, u)


@dataclass(frozen=True)
class ResGraph:
    V: FrozenSet[Vertex]
    λ: Mapping[Vertex, Vector]
    U: FrozenSet[Vertex]
    Φ: Phi

    def __post_init__(self) -> None:
        missing = set(self.V) - set(self.λ.keys())
        if missing:
            raise ValueError(f"labels missing for vertices: {missing}")
        if not self.V.issuperset(self.U):
            raise ValueError("U must be subset of V")
        if not self.λ:
            raise ValueError("labels must be provided for at least one vertex")
        dims = {len(v) for v in self.λ.values()}
        if len(dims) != 1:
            raise ValueError("all labels must have the same dimension")

    @property
    def E(self) -> FrozenSet[Edge]:
        vs = sorted(self.V)
        out: Set[Edge] = set()
        for i, u in enumerate(vs):
            for v in vs[i + 1 :]:
                if self.is_adjacent(u, v):
                    out.add((u, v))
        return frozenset(out)

    def is_adjacent(self, u: Vertex, v: Vertex) -> bool:
        return self.Φ(dot(self.λ[u], self.λ[v]))

    def neighbors(self, u: Vertex) -> FrozenSet[Vertex]:
        if u not in self.V:
            raise ValueError(f"unknown vertex: {u}")
        neigh: Set[Vertex] = set()
        for a, b in self.E:
            if a == u:
                neigh.add(b)
            elif b == u:
                neigh.add(a)
        return frozenset(neigh)

    @property
    def dimension(self) -> int:
        try:
            first = next(iter(self.λ.values()))
        except StopIteration as exc:
            raise ValueError("labels mapping is empty") from exc
        return len(first)
