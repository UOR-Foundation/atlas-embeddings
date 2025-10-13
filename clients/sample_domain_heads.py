#!/usr/bin/env python3
from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from views.api import load_atlas_from_json, view_r96_from_iota
from views.exceptional import view_E6, view_E7, view_E8, view_F4, view_G2


def main() -> None:
    atlas = load_atlas_from_json()
    views = [
        ("G2", view_G2),
        ("F4", view_F4),
        ("E6", view_E6),
        ("E7", view_E7),
        ("E8", view_E8),
    ]
    for tag, fn in views:
        view = fn(atlas)
        print(tag, view.meta["type"], view.meta["rank"])

    with open("data/iota_96.json", "r", encoding="utf-8") as fh:
        iota = json.load(fh)
    r96 = view_r96_from_iota(iota)
    print(
        "R96",
        r96.meta["n"],
        r96.meta["phi"],
        "deg_min",
        r96.meta["deg_min"],
        "deg_max",
        r96.meta["deg_max"],
    )


if __name__ == "__main__":
    main()
