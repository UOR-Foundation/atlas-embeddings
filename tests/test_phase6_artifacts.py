from __future__ import annotations

import json
import hashlib
import pathlib

from data.build_phase6 import build


def sha(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    h.update(path.read_bytes())
    return h.hexdigest()


def _resolve_manifest_path(out: pathlib.Path, path_value: str) -> pathlib.Path:
    path = pathlib.Path(path_value)
    if path.is_absolute():
        return path
    return (out / path).resolve()


def test_bit_for_bit_regeneration(tmp_path: pathlib.Path) -> None:
    iota = list(range(96))
    p_iota = tmp_path / "iota.json"
    p_iota.write_text(json.dumps(iota, separators=(",", ":")), encoding="utf-8")

    out1 = tmp_path / "out1"
    out2 = tmp_path / "out2"
    build(str(p_iota), str(out1))
    build(str(p_iota), str(out2))

    files1 = sorted(p for p in out1.rglob("*") if p.is_file())
    files2 = sorted(p for p in out2.rglob("*") if p.is_file())

    rel1 = [p.relative_to(out1) for p in files1]
    rel2 = [p.relative_to(out2) for p in files2]
    assert rel1 == rel2

    for a, b in zip(files1, files2):
        assert sha(a) == sha(b)


def test_manifest_lists_hashes(tmp_path: pathlib.Path) -> None:
    iota = list(range(96))
    p_iota = tmp_path / "iota.json"
    p_iota.write_text(json.dumps(iota, separators=(",", ":")), encoding="utf-8")

    out = tmp_path / "out"
    build(str(p_iota), str(out))

    manifest_path = out / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))

    assert "files" in manifest
    assert len(manifest["files"]) >= 7

    for rec in manifest["files"]:
        resolved = _resolve_manifest_path(out, rec["path"])
        assert resolved.exists()
        assert sha(resolved) == rec["sha256"]
