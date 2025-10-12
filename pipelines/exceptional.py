from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import permutations, product
from typing import Iterable, List, Optional

from core.resgraph import ResGraph, Vector, dot
from ops.closure import RC
from ops.filters import filter_vertices
from lie.simple_system import extract_simple_system
from lie.cartan import cartan_matrix
from lie.classify import identify_dynkin
from lie.weyl_order import weyl_order_for


@dataclass(frozen=True)
class ConstructionReport:
    type_name: str
    rank: int
    cartan: List[List[int]]
    weyl_order: int
    simple_roots: List[Vector]


def _collect_roots(G: ResGraph) -> List[Vector]:
    return [G.λ[v] for v in sorted(G.V)]


def _report_from_roots(
    roots: Iterable[Vector],
    simple_override: Optional[Iterable[Vector]] = None,
) -> ConstructionReport:
    roots_list = list(roots)
    if simple_override is None:
        simple = sorted(extract_simple_system(roots_list))
    else:
        simple = sorted(tuple(vec) for vec in simple_override)
    cartan = cartan_matrix(simple)
    dynkin = identify_dynkin(cartan)
    if dynkin == "Unknown":
        raise ValueError("unable to classify root system")
    return ConstructionReport(
        type_name=dynkin,
        rank=len(simple),
        cartan=cartan,
        weyl_order=weyl_order_for(dynkin),
        simple_roots=simple,
    )


def _phi_minus_one(t: Q) -> bool:
    return t == Q(-1)


def _build_graph_from_vectors(vectors: List[Vector]) -> ResGraph:
    names = [f"s{i}" for i in range(len(vectors))]
    lam = {name: vec for name, vec in zip(names, vectors)}
    return ResGraph(V=frozenset(names), λ=lam, U=frozenset(), Φ=_phi_minus_one)


def _generate_f4_simple_roots() -> List[Vector]:
    return [
        (Q(0), Q(1), Q(-1), Q(0)),
        (Q(0), Q(0), Q(1), Q(-1)),
        (Q(0), Q(0), Q(0), Q(1)),
        (Q(1, 2), Q(-1, 2), Q(-1, 2), Q(-1, 2)),
    ]


def _generate_g2_simple_roots() -> List[Vector]:
    return [
        (Q(1), Q(-1), Q(0)),
        (Q(-2), Q(1), Q(1)),
    ]


def _generate_f4_roots() -> List[Vector]:
    roots = set()
    for i in range(4):
        for j in range(i + 1, 4):
            for si in (-1, 1):
                for sj in (-1, 1):
                    v = [Q(0)] * 4
                    v[i] = Q(si)
                    v[j] = Q(sj)
                    roots.add(tuple(v))
    for i in range(4):
        for sgn in (-1, 1):
            v = [Q(0)] * 4
            v[i] = Q(sgn)
            roots.add(tuple(v))
    for signs in product((-1, 1), repeat=4):
        v = [Q(s, 2) for s in signs]
        roots.add(tuple(v))
    return sorted(roots)


def _generate_g2_roots() -> List[Vector]:
    roots = set()
    for i in range(3):
        for j in range(3):
            if i == j:
                continue
            v = [Q(0)] * 3
            v[i] = Q(1)
            v[j] = Q(-1)
            roots.add(tuple(v))
    for i, j, k in permutations(range(3), 3):
        if len({i, j, k}) < 3:
            continue
        v = [Q(0)] * 3
        v[i] = Q(2)
        v[j] = Q(-1)
        v[k] = Q(-1)
        roots.add(tuple(v))
        roots.add(tuple(-x for x in v))
    return sorted(roots)


def build_E8(A: ResGraph) -> ConstructionReport:
    closure = RC(A)
    return _report_from_roots(_collect_roots(closure))


def build_E7(A: ResGraph) -> ConstructionReport:
    G = RC(A)
    h = (Q(0),) * 6 + (Q(1), Q(1))
    filtered = filter_vertices(G, lambda _u, vec: dot(vec, h) == Q(0))
    closure = RC(filtered)
    return _report_from_roots(_collect_roots(closure))


def build_E6(A: ResGraph) -> ConstructionReport:
    G = RC(A)
    h1 = (Q(0),) * 6 + (Q(1), Q(1))
    h2 = (Q(0),) * 5 + (Q(1), Q(-1), Q(0))
    filtered = filter_vertices(G, lambda _u, vec: dot(vec, h1) == Q(0))
    filtered = filter_vertices(filtered, lambda _u, vec: dot(vec, h2) == Q(0))
    closure = RC(filtered)
    return _report_from_roots(_collect_roots(closure))


def build_F4(_A: ResGraph) -> ConstructionReport:
    simple = _generate_f4_simple_roots()
    base = _build_graph_from_vectors(simple)
    closure = RC(base)
    return _report_from_roots(_collect_roots(closure), simple_override=simple)


def build_G2(_A: ResGraph) -> ConstructionReport:
    simple = _generate_g2_simple_roots()
    base = _build_graph_from_vectors(simple)
    closure = RC(base)
    return _report_from_roots(_collect_roots(closure), simple_override=simple)
