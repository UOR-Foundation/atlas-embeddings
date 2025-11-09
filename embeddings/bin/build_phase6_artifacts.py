#!/usr/bin/env python3
from __future__ import annotations

import argparse
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from data.build_phase6 import build


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--iota", required=True)
    parser.add_argument("--out", default="artifacts/phase6")
    args = parser.parse_args()
    build(args.iota, args.out)


if __name__ == "__main__":
    main()
