from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict

from core.resgraph import ResGraph


@dataclass(frozen=True)
class View:
    """Lightweight container describing a residual graph view."""

    name: str
    graph: ResGraph
    meta: Dict[str, Any]
