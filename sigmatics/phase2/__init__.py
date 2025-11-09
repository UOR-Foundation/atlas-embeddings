"""
Phase 2 — Executor and Evaluator (Sigmatics × Multiplicity)

This module implements the Phase 2 executor and evaluator for the Sigmatics
compiler pipeline, providing:

- Executor: Signal and relation path operations
- Evaluator: Resonance metrics and baseline comparisons
- JSONL trace logging
- Metrics computation (EVR, retrieval uplift, relation consistency)
"""

from .executor import (
    Executor,
    ExecState,
    Policies,
    Trace,
    run,
    admissible,
    N,
    PAGE_SIZE,
    PAGES,
)

__all__ = [
    "Executor",
    "ExecState", 
    "Policies",
    "Trace",
    "run",
    "admissible",
    "N",
    "PAGE_SIZE",
    "PAGES",
]
