from __future__ import annotations

from typing import List

from core.resgraph import ResGraph, Vertex, Vector


def _direct_sum(x: Vector, y: Vector) -> Vector:
    return tuple(list(x) + list(y))


def product(G1: ResGraph, G2: ResGraph) -> ResGraph:
    """Return the resonance product ``G1 ⊠ G2``.

    The vertex set is the Cartesian product of the vertices of ``G1`` and
    ``G2``.  Labels are concatenated to form an orthogonal direct sum and the
    adjacency predicate ``Φ`` is re-used from the first factor (the pipeline
    guarantees compatibility).
    """
    vertices: List[Vertex] = []
    lam = {}
    for u in sorted(G1.V):
        for v in sorted(G2.V):
            name = f"({u},{v})"
            vertices.append(name)
            lam[name] = _direct_sum(G1.λ[u], G2.λ[v])
    U = frozenset(f"({u},{v})" for u in G1.U for v in G2.U)
    return ResGraph(V=frozenset(vertices), λ=lam, U=U, Φ=G1.Φ)
