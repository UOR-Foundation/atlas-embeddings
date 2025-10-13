from __future__ import annotations

import json
from fractions import Fraction as Q
from pathlib import Path
from typing import Dict, Iterable, Sequence

from core.resgraph import ResGraph, Vector
from views.phi import phi_minus1, phi_plus1
from views.types import View
from e8.roots import generate_e8_roots
from atlas.atlas import make_atlas


AtlasJson = Dict[str, Iterable]


def _parse_fraction_sequence(seq: Sequence[str]) -> Vector:
    return tuple(Q(item) for item in seq)


def load_atlas_from_json(path: str | Path = "data/atlas_min.json") -> ResGraph:
    """Load a residual graph produced by the Atlas pipeline."""

    path = Path(path)
    with path.open("r", encoding="utf-8") as fh:
        data: AtlasJson = json.load(fh)

    V = frozenset(data["V"])
    U = frozenset(data.get("U", []))
    labels_dict: Dict[str, Vector] = {
        vertex: _parse_fraction_sequence(coords)
        for vertex, coords in data["labels"].items()
    }
    return make_atlas(V, labels_dict, U)


def make_resgraph_from_vectors(
    vecs: Sequence[Vector], *, name_prefix: str = "v", phi=phi_minus1
) -> ResGraph:
    """Build a residual graph whose vertices are named vectors with Φ predicate."""

    names = [f"{name_prefix}{i}" for i in range(len(vecs))]
    lam: Dict[str, Vector] = {name: tuple(vec) for name, vec in zip(names, vecs)}
    return ResGraph(V=frozenset(names), λ=lam, U=frozenset(), Φ=phi)


def view_r96_from_iota(iota: Sequence[int]) -> View:
    """Construct the Φ=+1 view on the R96 configuration of E8 roots."""

    roots = generate_e8_roots()
    selected = [roots[index] for index in iota]
    graph = make_resgraph_from_vectors(selected, name_prefix="r", phi=phi_plus1)

    degrees = [len(graph.neighbors(vertex)) for vertex in sorted(graph.V)]
    deg_min = min(degrees) if degrees else 0
    deg_max = max(degrees) if degrees else 0
    deg_sum = sum(degrees)
    deg_count = len(degrees) if degrees else 1

    meta = {
        "n": len(selected),
        "deg_min": deg_min,
        "deg_max": deg_max,
        "deg_avg_num": deg_sum,
        "deg_avg_den": deg_count,
        "phi": "+1",
        "cayley_free": True,
    }
    return View(name="R96(+1)", graph=graph, meta=meta)


