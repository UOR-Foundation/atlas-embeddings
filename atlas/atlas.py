from __future__ import annotations

from fractions import Fraction as Q
from typing import Dict, FrozenSet

from core.resgraph import ResGraph, Vertex, Vector


def phi_atlas(t: Q) -> bool:
    return t == Q(-1)


def make_atlas(
    V: FrozenSet[Vertex],
    labels: Dict[Vertex, Vector],
    U: FrozenSet[Vertex],
) -> ResGraph:
    return ResGraph(V=V, λ=labels, U=U, Φ=phi_atlas)
