#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json

from r96.build import build_r96
from r96.io import save_artifacts


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--iota", required=True, help="Path to JSON list of 96 E8 root indices")
    parser.add_argument("--out", default="artifacts/phase3", help="Output directory for artifacts")
    parser.add_argument(
        "--closure-negation",
        action="store_true",
        help="Duplicate vertices with sign flip; no cross-copy edges",
    )
    args = parser.parse_args()

    with open(args.iota, "r", encoding="utf-8") as fh:
        iota = json.load(fh)

    graph = build_r96(iota=iota, closure_negation=args.closure_negation)
    save_artifacts(args.out, graph)

    print(
        "OK",
        f"n={graph.csr.n}",
        f"edges={graph.edges}",
        f"deg_min={min(graph.degrees)}",
        f"deg_max={max(graph.degrees)}",
        f"deg_avg={sum(graph.degrees) / len(graph.degrees):.6f}",
        f"cayley_free={graph.cayley_free}",
        f"negation_closed={graph.negation_closed}",
    )


if __name__ == "__main__":
    main()
