#!/usr/bin/env python3
from __future__ import annotations

import json
import pathlib

from atlas.atlas import make_atlas
from atlas.embedding import embed_atlas_to_e8
from core.resgraph import ResGraph
from fractions import Fraction as Q


def load_atlas() -> ResGraph:
    data_path = pathlib.Path("data/atlas_min.json")
    data = json.loads(data_path.read_text())
    V = frozenset(data["V"])
    U = frozenset(data["U"])
    labels = {k: tuple(Q(n) for n in v) for k, v in data["labels"].items()}
    return make_atlas(V, labels, U)


def main() -> None:
    atlas = load_atlas()
    res = embed_atlas_to_e8(atlas)
    outdir = pathlib.Path("artifacts/phase2")
    outdir.mkdir(parents=True, exist_ok=True)

    with open(outdir / "embedding.json", "w") as fh:
        json.dump({"f": res.f, "checksum_coords": res.checksum_coords}, fh, indent=2)

    with open(outdir / "coordinates.csv", "w") as fh:
        for u in sorted(atlas.V):
            row = ",".join(str(x) for x in res.roots[res.f[u]])
            fh.write(f"{u},{row}\n")

    (outdir / "proof.log").write_text(res.log, encoding="utf-8")
    print("OK", res.checksum_coords)


if __name__ == "__main__":
    main()
