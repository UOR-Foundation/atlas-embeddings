from __future__ import annotations
import hashlib, json, os, pathlib, subprocess, sys
from typing import Iterable, List, Dict


def sha256_file(p: pathlib.Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def git_meta() -> Dict[str, str]:
    def run(*args):
        return subprocess.check_output(args, text=True).strip()

    try:
        return {
            "git_commit": run("git", "rev-parse", "HEAD"),
            "git_tree": run("git", "write-tree"),
            "git_status_clean": "1" if run("git", "status", "--porcelain") == "" else "0",
        }
    except Exception:
        return {
            "git_commit": "unknown",
            "git_tree": "unknown",
            "git_status_clean": "unknown",
        }


def deps_meta() -> Dict[str, str]:
    import platform, pkgutil
    import importlib

    vers = {}
    for name in ["numpy", "networkx"]:
        try:
            m = importlib.import_module(name)
            vers[name] = getattr(m, "__version__", "unknown")
        except Exception:
            vers[name] = "missing"
    return {
        "python": sys.version.split()[0],
        **{f"dep_{k}": v for k, v in vers.items()},
    }


def record_manifest(paths: Iterable[pathlib.Path], root: pathlib.Path, meta: Dict[str, str]) -> Dict:
    items = []
    for p in sorted(paths, key=lambda x: str(x.relative_to(root))):
        items.append(
            {
                "path": str(p.relative_to(root)).replace("\\", "/"),
                "sha256": sha256_file(p),
                "bytes": p.stat().st_size,
            }
        )
    return {"meta": meta, "files": items}
