from __future__ import annotations

from typing import Dict, List

from r96.build import build_r96


def r96_stats(iota: List[int]) -> Dict[str, int | bool]:
    graph = build_r96(iota=iota, closure_negation=False)
    degrees = graph.degrees
    degree_sum = sum(degrees)
    n = graph.csr.n
    return {
        "n": n,
        "edges": graph.edges,
        "deg_min": min(degrees),
        "deg_max": max(degrees),
        "deg_sum": degree_sum,
        "deg_avg_num": degree_sum,
        "deg_avg_den": n,
        "cayley_free": graph.cayley_free,
    }
