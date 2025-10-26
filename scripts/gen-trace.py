#!/usr/bin/env python3
import csv
import os
from typing import Iterable

try:
    import yaml
except Exception as exc:  # pragma: no cover - we expect PyYAML in dev environments
    raise RuntimeError("PyYAML is required to generate the trace matrix") from exc

ROOT = os.path.dirname(os.path.dirname(__file__))
INV_PATH = os.path.join(ROOT, "docs", "specs", "v2", "invariants.yaml")
OUT_PATH = os.path.join(ROOT, "docs", "trace", "matrix.csv")


def iter_rows() -> Iterable[tuple[str, str, str, str, str]]:
    with open(INV_PATH, "r", encoding="utf-8") as handle:
        data = yaml.safe_load(handle)

    rows = [("spec_id", "obligation_id", "proof_artifact", "test_id", "code_ref")]
    for inv in data.get("invariants", []):
        spec_id = inv.get("id", "")
        for obl in inv.get("obligation_ids", []):
            proof = f"docs/proofs/obl/{obl.split('.')[-1]}.md"
            for test in inv.get("test_bindings", []):
                rows.append((spec_id, obl, proof, test, "SRC:TBD"))
    return rows


def main() -> None:
    rows = list(iter_rows())
    os.makedirs(os.path.dirname(OUT_PATH), exist_ok=True)
    with open(OUT_PATH, "w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerows(rows)
    print(f"trace written: {OUT_PATH}")

if __name__ == "__main__":
    main()
