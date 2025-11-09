from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping

from .resgraph import ResGraph, Vertex
from .weyl import WeylAction


@dataclass(frozen=True)
class Morphism:
    src: ResGraph
    dst: ResGraph
    f: Mapping[Vertex, Vertex]
    w: WeylAction

    def check(self) -> None:
        s, t = self.src, self.dst
        if set(self.f.keys()) != set(s.V):
            raise ValueError("f must map every source vertex")
        if not set(self.f.values()).issubset(t.V):
            raise ValueError("f maps to unknown target vertices")
        for (u, v) in s.E:
            u2, v2 = self.f[u], self.f[v]
            if not t.is_adjacent(u2, v2):
                raise ValueError(f"edge not preserved: {(u, v)} → {(u2, v2)}")
        for u in s.V:
            lu = s.λ[u]
            lhs = t.λ[self.f[u]]
            rhs = self.w.apply(lu)
            if lhs != rhs:
                raise ValueError(
                    f"label mismatch at {u}: {lhs} != w·λ({u})={rhs}"
                )
        imageU = {self.f[u] for u in s.U}
        if not imageU.issubset(t.U):
            raise ValueError("unity not preserved: f(U_src) ⊆ U_dst fails")
