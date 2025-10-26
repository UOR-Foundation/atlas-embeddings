#!/usr/bin/env python3
import sys
import json
import os

try:
    import yaml
except Exception:
    yaml = None

ROOT = os.path.dirname(os.path.dirname(__file__))

def load_yaml(path: str):
    if yaml is None:
        raise RuntimeError("PyYAML is required for spec_check")
    with open(path, "r", encoding="utf-8") as handle:
        return yaml.safe_load(handle)

def main() -> None:
    inv_path = os.path.join(ROOT, "docs", "specs", "v2", "invariants.yaml")
    schema_path = os.path.join(ROOT, "schemas", "spec.schema.json")

    try:
        data = load_yaml(inv_path)
    except Exception as exc:
        print(f"Failed to load {inv_path}: {exc}", file=sys.stderr)
        sys.exit(2)

    try:
        with open(schema_path, "r", encoding="utf-8") as handle:
            schema = json.load(handle)
    except Exception as exc:
        print(f"Failed to load schema {schema_path}: {exc}", file=sys.stderr)
        sys.exit(2)

    if "invariants" not in data or not isinstance(data["invariants"], list):
        print("Invalid: invariants missing or not a list", file=sys.stderr)
        sys.exit(2)

    req_keys = {
        "id",
        "statement",
        "model_ref",
        "obligation_ids",
        "test_bindings",
        "owner",
        "status",
    }
    ok = True
    for inv in data["invariants"]:
        missing = req_keys - set(inv.keys())
        if missing:
            print(f"Invalid invariant {inv.get('id')}: missing {sorted(missing)}", file=sys.stderr)
            ok = False
            continue

        model_rel = inv["model_ref"]
        model_path = os.path.join(ROOT, "docs", "specs", "v2", model_rel)
        if not os.path.exists(model_path):
            print(f"Model missing for {inv['id']}: {model_rel}", file=sys.stderr)
            ok = False

    if not ok:
        sys.exit(2)

    print("spec-check: OK")

if __name__ == "__main__":
    main()
