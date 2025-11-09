import json
import pathlib
import subprocess
import sys


def test_validate_runs_and_writes_certificate(tmp_path: pathlib.Path) -> None:
    iota = list(range(96))
    iota_path = tmp_path / "iota.json"
    iota_path.write_text(json.dumps(iota, separators=(",", ":")), encoding="utf-8")

    out_dir = tmp_path / "out"
    cmd = [
        sys.executable,
        "bin/validate.py",
        "--iota",
        str(iota_path),
        "--out",
        str(out_dir),
        "--induced-limit",
        "10",
    ]
    result = subprocess.run(cmd, capture_output=True, text=True)

    assert result.returncode == 0
    assert (out_dir / "validation.json").exists()
    assert (out_dir / "validation.sha256").exists()
    stdout = result.stdout
    assert "E1" in stdout
    assert "E2" in stdout
    assert "E3" in stdout
    assert "CERT" in stdout
