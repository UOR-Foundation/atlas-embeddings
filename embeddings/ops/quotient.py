from __future__ import annotations

from typing import Callable, Dict, Iterable, List, Tuple

from core.resgraph import ResGraph, Vertex

Symmetry = Callable[[Vertex], Vertex]


def quotient(G: ResGraph, H: Iterable[Symmetry]) -> ResGraph:
    """Form the quotient of ``G`` by the symmetry group ``H``.

    Vertices that lie in the same orbit under the action of ``H`` are merged;
    labels must agree across every orbit.  Vertex representatives are named by
    listing the orbit elements in lexicographic order.
    """

    parent: Dict[Vertex, Vertex] = {}

    def find(x: Vertex) -> Vertex:
        parent.setdefault(x, x)
        if parent[x] != x:
            parent[x] = find(parent[x])
        return parent[x]

    def unite(a: Vertex, b: Vertex) -> None:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[rb] = ra

    for sym in H:
        for v in G.V:
            unite(v, sym(v))

    classes: Dict[Vertex, List[Vertex]] = {}
    for v in G.V:
        root = find(v)
        classes.setdefault(root, []).append(v)

    vertices: List[Vertex] = []
    lam: Dict[Vertex, Tuple] = {}
    Uq = set()

    for _, orbit in sorted(classes.items(), key=lambda kv: tuple(sorted(kv[1]))):
        orbit_sorted = sorted(orbit)
        representative = orbit_sorted[0]
        label = G.λ[representative]
        for w in orbit_sorted[1:]:
            if G.λ[w] != label:
                raise ValueError("non-invariant labels in orbit")
        name = f"[{','.join(orbit_sorted)}]"
        vertices.append(name)
        lam[name] = label
        if any(v in G.U for v in orbit_sorted):
            Uq.add(name)

    return ResGraph(V=frozenset(vertices), λ=lam, U=frozenset(Uq), Φ=G.Φ)
