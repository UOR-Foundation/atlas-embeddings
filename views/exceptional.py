from __future__ import annotations

from typing import Iterable

from core.resgraph import ResGraph, Vector
from lie.cartan import cartan_matrix
from lie.classify import identify_dynkin
from pipelines.exceptional import build_E6, build_E7, build_E8, build_F4, build_G2
from views.api import make_resgraph_from_vectors
from views.phi import phi_minus1
from views.types import View


def _simple_roots_view(simple: Iterable[Vector], tag: str) -> View:
    simple_list = list(simple)
    graph = make_resgraph_from_vectors(simple_list, name_prefix=f"{tag}_α", phi=phi_minus1)
    cartan = cartan_matrix(simple_list)
    return View(
        name=f"{tag}_Dynkin",
        graph=graph,
        meta={
            "type": identify_dynkin(cartan),
            "rank": len(simple_list),
            "phi": "−1",
            "cartan": cartan,
        },
    )


def view_G2(_A: ResGraph) -> View:
    report = build_G2(_A)
    return _simple_roots_view(report.simple_roots, "G2")


def view_F4(_A: ResGraph) -> View:
    report = build_F4(_A)
    return _simple_roots_view(report.simple_roots, "F4")


def view_E6(_A: ResGraph) -> View:
    report = build_E6(_A)
    return _simple_roots_view(report.simple_roots, "E6")


def view_E7(_A: ResGraph) -> View:
    report = build_E7(_A)
    return _simple_roots_view(report.simple_roots, "E7")


def view_E8(_A: ResGraph) -> View:
    report = build_E8(_A)
    return _simple_roots_view(report.simple_roots, "E8")
