from __future__ import annotations

import json
import pathlib

import numpy as np

from core.arithmetic import Q as _Q
from .build import CSR, R96Graph


def save_artifacts(outdir: str, g: R96Graph) -> None:
    """Persist the CSR structure and degree statistics for an R96 graph."""

    path = pathlib.Path(outdir)
    path.mkdir(parents=True, exist_ok=True)

    np.savez_compressed(
        path / "r96_csr.npz",
        n=g.csr.n,
        indptr=np.array(g.csr.indptr, dtype=np.int64),
        indices=np.array(g.csr.indices, dtype=np.int64),
        data=np.array(g.csr.data, dtype=np.int8),
    )

    avg = _Q(sum(g.degrees), len(g.degrees)) if g.degrees else _Q(0)
    degree_stats = {
        "n": g.csr.n,
        "edges": g.edges,
        "degree_min": int(min(g.degrees)) if g.degrees else 0,
        "degree_max": int(max(g.degrees)) if g.degrees else 0,
        "degree_avg": {"numerator": avg.numerator, "denominator": avg.denominator},
        "cayley_free": g.cayley_free,
        "negation_closed": g.negation_closed,
    }

    (path / "degree_stats.json").write_text(
        json.dumps(degree_stats, indent=2),
        encoding="utf-8",
    )
