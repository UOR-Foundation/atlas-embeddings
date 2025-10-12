from __future__ import annotations

import json

import numpy as np

from r96.build import build_r96
from r96.io import save_artifacts


def test_r96_core_counts_and_flag(tmp_path):
    iota = list(range(96))
    graph = build_r96(iota=iota, closure_negation=False)

    assert graph.csr.n == 96
    assert graph.cayley_free is True

    assert len(graph.csr.indptr) == graph.csr.n + 1
    assert len(graph.csr.indices) == sum(graph.degrees)
    assert graph.edges == sum(graph.degrees) // 2

    assert min(graph.degrees) >= 0
    assert max(graph.degrees) <= 95

    outdir = tmp_path / "artifacts"
    save_artifacts(str(outdir), graph)

    csr_file = outdir / "r96_csr.npz"
    assert csr_file.exists()
    npz = np.load(csr_file)
    assert npz["n"] == graph.csr.n
    assert np.array_equal(npz["indptr"], np.array(graph.csr.indptr))
    assert np.array_equal(npz["indices"], np.array(graph.csr.indices))
    assert np.array_equal(npz["data"], np.array(graph.csr.data))

    stats = json.loads((outdir / "degree_stats.json").read_text())
    assert stats["cayley_free"] is True
    assert stats["negation_closed"] is False
    assert stats["degree_avg"]["denominator"] > 0


def test_negation_closure_no_edge_changes_structure():
    iota = list(range(96))
    base = build_r96(iota=iota, closure_negation=False)
    doubled = build_r96(iota=iota, closure_negation=True)

    assert doubled.csr.n == 192
    assert sorted(base.degrees + base.degrees) == sorted(doubled.degrees)
    assert doubled.negation_closed is True
