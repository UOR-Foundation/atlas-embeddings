from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import List

from e8.roots import generate_e8_roots, dot


@dataclass(frozen=True)
class CSR:
    """Compressed sparse row representation of an unweighted simple graph."""

    n: int
    indptr: List[int]
    indices: List[int]
    data: List[int]


@dataclass(frozen=True)
class R96Graph:
    """Container for the R96 Phase 3 graph and related metadata."""

    csr: CSR
    degrees: List[int]
    edges: int
    cayley_free: bool
    negation_closed: bool


def _csr_from_adj(adj: List[List[int]]) -> CSR:
    indptr: List[int] = [0]
    indices: List[int] = []
    data: List[int] = []
    for nbrs in adj:
        indices.extend(nbrs)
        data.extend([1] * len(nbrs))
        indptr.append(len(indices))
    return CSR(n=len(adj), indptr=indptr, indices=indices, data=data)


def _degree_stats_from_adj(adj: List[List[int]]) -> List[int]:
    return [len(nbrs) for nbrs in adj]


def build_r96(iota: List[int], closure_negation: bool = False) -> R96Graph:
    """Construct the Phase 3 R96 graph using a subset of E8 roots.

    Parameters
    ----------
    iota:
        Indices selecting a 96-element subset of the 240 E8 roots.
    closure_negation:
        When ``True`` the graph is duplicated to include the negated roots as a
        disjoint copy with identical adjacency.
    """

    roots = generate_e8_roots()  # Deterministic ordering of the 240 E8 roots.
    if len(iota) != 96:
        raise ValueError("iota must contain exactly 96 indices")

    subset = [roots[k] for k in iota]

    # Build adjacency lists for +1 inner products.
    adj: List[List[int]] = [[] for _ in range(96)]
    for i in range(96):
        for j in range(i + 1, 96):
            if dot(subset[i], subset[j]) == Q(1):
                adj[i].append(j)
                adj[j].append(i)

    # Sort adjacency lists for deterministic CSR output.
    for nbrs in adj:
        nbrs.sort()

    negation_closed = False
    if closure_negation:
        n = len(adj)
        adj_extended: List[List[int]] = []
        for nbrs in adj:
            adj_extended.append(nbrs[:])
        for nbrs in adj:
            adj_extended.append([v + n for v in nbrs])
        adj = adj_extended
        negation_closed = True

    csr = _csr_from_adj(adj)
    degrees = _degree_stats_from_adj(adj)
    edges = sum(degrees) // 2

    cayley_free = True  # Constructed using only +1 inner products within E8.

    return R96Graph(
        csr=csr,
        degrees=degrees,
        edges=edges,
        cayley_free=cayley_free,
        negation_closed=negation_closed,
    )
