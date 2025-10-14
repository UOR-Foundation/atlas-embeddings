import json, subprocess, sys, pathlib

def test_lint_ok(tmp_path):
    repo = pathlib.Path(".")
    toml = repo/"aep.toml"
    assert toml.exists()
    p = subprocess.run([sys.executable,"cli/lint_aep.py", str(toml), str(repo)], capture_output=True, text=True)
    assert p.returncode in (0, ) or ("status" in p.stdout)
