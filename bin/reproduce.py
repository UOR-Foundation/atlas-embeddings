#!/usr/bin/env python3
from __future__ import annotations
import json, os, pathlib, sys

ROOT = pathlib.Path(".").resolve()
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.manifest import git_meta, deps_meta, record_manifest

os.environ["PYTHONHASHSEED"] = "0"
os.environ["LC_ALL"] = "C"
os.environ["TZ"] = "UTC"

ART = ROOT / "artifacts"


def clean_dir(p: pathlib.Path):
    if p.exists():
        for q in sorted(p.rglob("*"), reverse=True):
            if q.is_file():
                q.unlink()
            else:
                try:
                    q.rmdir()
                except Exception:
                    pass
    p.mkdir(parents=True, exist_ok=True)


def main():
    # canonical inputs
    iota_path = ROOT / "data" / "iota_96.json"
    if not iota_path.exists():
        print("missing data/iota_96.json", file=sys.stderr)
        sys.exit(2)

    # Phase 2
    clean_dir(ART / "phase2")
    from bin.embed_atlas_to_e8 import main as embed_main

    sys.argv = ["embed_atlas_to_e8.py"]  # prevent argparse noise
    embed_main()

    # Phase 3
    clean_dir(ART / "phase3")
    from r96.build import build_r96
    from r96.io import save_artifacts
    import json as _json

    iota = _json.loads(iota_path.read_text())
    g = build_r96(iota=iota, closure_negation=False)
    save_artifacts(str(ART / "phase3"), g)

    # Phase 4
    clean_dir(ART / "phase4")
    from bin.run_constructions import main as run_constructions

    sys.argv = ["run_constructions.py"]
    run_constructions()

    # Phase 6 (publishes canonical artifacts + hashes)
    clean_dir(ART / "phase6")
    from data.build_phase6 import build as build_p6

    build_p6(str(iota_path), str(ART / "phase6"))

    # Phase 7 (validator and certificate)
    clean_dir(ART / "phase7")
    from bin.validate import main as validate_main

    sys.argv = [
        "validate.py",
        "--iota",
        str(iota_path),
        "--out",
        str(ART / "phase7"),
        "--induced-limit",
        "1000",
    ]
    validate_main()

    # Aggregate manifest
    produced = []
    for sub in ["phase2", "phase3", "phase4", "phase6", "phase7"]:
        for p in (ART / sub).rglob("*"):
            if p.is_file():
                produced.append(p)
    manifest = record_manifest(produced, ROOT, {**git_meta(), **deps_meta()})
    (ART / "manifest.current.json").write_text(json.dumps(manifest, indent=2), encoding="utf-8")

    # If a lock exists, compare and fail on drift
    lock = ART / "manifest.lock.json"
    if lock.exists():
        want = json.loads(lock.read_text(encoding="utf-8"))
        have = manifest
        if want["files"] != have["files"]:
            print("DRIFT: artifacts differ from lockfile", file=sys.stderr)
            # show first difference
            wf = {x["path"]: x for x in want["files"]}
            hf = {x["path"]: x for x in have["files"]}
            paths = sorted(set(wf) | set(hf))
            for path in paths:
                a, b = wf.get(path), hf.get(path)
                if a != b:
                    print(f"- {path}\n  lock: {a}\n  curr: {b}", file=sys.stderr)
                    break
            sys.exit(3)

    # Write or refresh lock if env allows (local dev)
    if os.environ.get("WRITE_LOCK", "0") == "1":
        (ART / "manifest.lock.json").write_text(json.dumps(manifest, indent=2), encoding="utf-8")

    print("reproduce: OK")


if __name__ == "__main__":
    main()
