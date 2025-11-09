from __future__ import annotations

from typing import Callable, Dict

from core.resgraph import ResGraph, Vertex, Vector

PredV = Callable[[Vertex, Vector], bool]


def filter_vertices(G: ResGraph, pred: PredV) -> ResGraph:
    """Return the induced subgraph on vertices satisfying ``pred``."""
    vertices = [v for v in sorted(G.V) if pred(v, G.λ[v])]
    lam = {v: G.λ[v] for v in vertices}
    U = frozenset(v for v in vertices if v in G.U)
    return ResGraph(V=frozenset(vertices), λ=lam, U=U, Φ=G.Φ)


def augment_vertices(G: ResGraph, new_items: Dict[Vertex, Vector]) -> ResGraph:
    """Add the ``new_items`` to ``G`` while preserving determinism."""
    vertices = set(G.V)
    lam = dict(G.λ)
    for name, vec in new_items.items():
        if name in vertices:
            raise ValueError(f"duplicate vertex {name}")
        vertices.add(name)
        lam[name] = vec
    Vsorted = sorted(vertices)
    return ResGraph(V=frozenset(Vsorted), λ=lam, U=G.U, Φ=G.Φ)
