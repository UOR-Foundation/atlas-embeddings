"""
Phase 4 — Three-Week Timeline & Ship Plan

Consolidates Phases 1-3 into a complete, reproducible release package.
"""

__version__ = "0.1.0"

from .phase4 import (
    generate_index_map_examples,
    generate_kpis,
    generate_report,
    run_full_pipeline,
)

__all__ = [
    "generate_index_map_examples",
    "generate_kpis",
    "generate_report",
    "run_full_pipeline",
]
