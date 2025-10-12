#!/usr/bin/env python3
from __future__ import annotations

import json
import pathlib
import sys
from fractions import Fraction as Q

ROOT = pathlib.Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from atlas.atlas import make_atlas
from pipelines.exceptional import build_E6, build_E7, build_E8, build_F4, build_G2


def _load_from_file(path: pathlib.Path):
    data = json.loads(path.read_text())
    V = frozenset(data["V"])
    U = frozenset(data.get("U", []))
    labels = {k: tuple(Q(x) for x in v) for k, v in data["labels"].items()}
    return make_atlas(V, labels, U)


def _synthetic_atlas():
    from e8.roots import generate_e8_roots

    roots = generate_e8_roots()
    verts = [f"v{i}" for i in range(96)]
    labels = {name: roots[i] for i, name in enumerate(verts)}
    return make_atlas(frozenset(verts), labels, frozenset())


def load_atlas():
    path = pathlib.Path("data/atlas_min.json")
    if path.exists():
        return _load_from_file(path)
    return _synthetic_atlas()


def write_report(name: str, report) -> None:
    out_dir = pathlib.Path("artifacts/phase4") / name
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "cartan.json").write_text(json.dumps(report.cartan, indent=2), encoding="utf-8")
    meta = {"type": report.type_name, "rank": report.rank, "weyl_order": report.weyl_order}
    (out_dir / "meta.json").write_text(json.dumps(meta, indent=2), encoding="utf-8")


def main() -> None:
    atlas = load_atlas()
    builders = {
        "G2": build_G2,
        "F4": build_F4,
        "E6": build_E6,
        "E7": build_E7,
        "E8": build_E8,
    }
    for name, fn in builders.items():
        report = fn(atlas)
        write_report(name, report)
        print(name, report.type_name, report.weyl_order)


if __name__ == "__main__":
    main()
