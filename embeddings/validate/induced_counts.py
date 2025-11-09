from __future__ import annotations

from fractions import Fraction as Q
from typing import Dict, List, Tuple, Set

from e8.roots import dot

Vector = Tuple[Q, ...]


def _host_adjacency(vecs: List[Vector]) -> List[Set[int]]:
    n = len(vecs)
    adj: List[Set[int]] = [set() for _ in range(n)]
    for i in range(n):
        vi = vecs[i]
        for j in range(i + 1, n):
            if dot(vi, vecs[j]) == Q(-1):
                adj[i].add(j)
                adj[j].add(i)
    return adj


def _pattern_adjacency(name: str) -> List[Set[int]]:
    if name == "E6":
        edges = [(0, 1), (1, 2), (2, 3), (3, 4), (2, 5)]
    elif name == "E7":
        edges = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (2, 6)]
    elif name == "E8":
        edges = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (2, 7)]
    else:
        raise ValueError(f"unknown pattern {name}")
    node_count = max(max(u, v) for u, v in edges) + 1
    adj: List[Set[int]] = [set() for _ in range(node_count)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _validate_induced(mapping: Dict[int, int], host: List[Set[int]], pattern: List[Set[int]]) -> bool:
    nodes = list(mapping.keys())
    for i in range(len(nodes)):
        u = nodes[i]
        for j in range(i + 1, len(nodes)):
            v = nodes[j]
            host_has = mapping[v] in host[mapping[u]]
            pattern_has = v in pattern[u]
            if host_has != pattern_has:
                return False
    return True


def induced_subgraph_count(vecs: List[Vector], name: str, limit: int | None = None) -> int:
    host = _host_adjacency(vecs)
    pattern = _pattern_adjacency(name)

    order = sorted(range(len(pattern)), key=lambda x: len(pattern[x]), reverse=True)
    seen: Set[frozenset[int]] = set()

    def backtrack(idx: int, mapping: Dict[int, int], used: Set[int]) -> None:
        if limit is not None and len(seen) >= limit:
            return
        if idx == len(order):
            if _validate_induced(mapping, host, pattern):
                seen.add(frozenset(mapping.values()))
            return

        node = order[idx]
        candidate_sets: List[Set[int]] = []
        for nbr in pattern[node]:
            if nbr in mapping:
                candidate_sets.append(host[mapping[nbr]])
        if candidate_sets:
            candidates = set.intersection(*candidate_sets)
        else:
            candidates = set(range(len(host)))

        candidates -= used

        required_degree = len(pattern[node])
        for cand in sorted(candidates):
            if len(host[cand]) < required_degree:
                continue
            consistent = True
            for other, mapped in mapping.items():
                host_has = cand in host[mapped]
                pattern_has = other in pattern[node]
                if host_has != pattern_has:
                    consistent = False
                    break
            if not consistent:
                continue
            mapping[node] = cand
            used.add(cand)
            backtrack(idx + 1, mapping, used)
            used.remove(cand)
            del mapping[node]

    backtrack(0, {}, set())
    return len(seen)
