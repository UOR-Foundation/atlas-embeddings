#!/usr/bin/env python3
import json
import os
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
INCLUDE = [ROOT / "src" / "tcb", ROOT / "gen" / "tcb"]
EXCLUDE_PREFIXES = [ROOT / "tests", ROOT / "examples"]

def count_loc(path: pathlib.Path) -> int:
    total = 0
    if not path.exists():
        return 0
    for entry in path.rglob("*"):
        if not entry.is_file():
            continue
        if any(str(entry).startswith(str(ex)) for ex in EXCLUDE_PREFIXES):
            continue
        try:
            with entry.open("r", errors="ignore") as handle:
                total += sum(1 for _ in handle)
        except OSError:
            continue
    return total

def main() -> None:
    tcb_loc = sum(count_loc(path) for path in INCLUDE)
    total_loc = 0
    for entry in ROOT.rglob("*"):
        if not entry.is_file():
            continue
        if any(str(entry).startswith(str(ex)) for ex in EXCLUDE_PREFIXES):
            continue
        try:
            with entry.open("r", errors="ignore") as handle:
                total_loc += sum(1 for _ in handle)
        except OSError:
            continue

    ratio = (tcb_loc / total_loc) if total_loc else 0.0
    print(json.dumps({"tcb_loc": tcb_loc, "total_loc": total_loc, "ratio": ratio}, indent=2))

    budget = float(os.environ.get("TCB_BUDGET", "0.05"))
    if ratio > budget:
        print(f"TCB ratio {ratio:.3f} exceeds budget {budget}", file=sys.stderr)
        sys.exit(2)

if __name__ == "__main__":
    main()
