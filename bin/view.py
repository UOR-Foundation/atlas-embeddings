#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from views.api import load_atlas_from_json, view_r96_from_iota
from views.exceptional import view_E6, view_E7, view_E8, view_F4, view_G2


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--atlas", default="data/atlas_min.json")
    parser.add_argument("--r96-iota", dest="r96_iota", default=None)
    args = parser.parse_args()

    atlas = load_atlas_from_json(args.atlas)
    for tag, fn in [
        ("G2", view_G2),
        ("F4", view_F4),
        ("E6", view_E6),
        ("E7", view_E7),
        ("E8", view_E8),
    ]:
        view = fn(atlas)
        print(tag, view.meta["type"], view.meta["rank"])

    if args.r96_iota:
        with open(args.r96_iota, "r", encoding="utf-8") as fh:
            iota = json.load(fh)
        view = view_r96_from_iota(iota)
        print("R96", view.meta)


if __name__ == "__main__":
    main()
