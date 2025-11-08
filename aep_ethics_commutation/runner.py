#!/usr/bin/env python3
"""
Ethics Commutation AEP Runner

Validates:
1. Commutator [M, E_α] has norm ≤ atol
2. All forbidden Δ-channels have magnitude ≤ atol
3. Generates deterministic proof and verifies it
4. Exits 0 on pass, 2 on invariant violation
"""
from __future__ import annotations

import fnmatch
import json
import os
import sys
import time
from pathlib import Path
from typing import Any

try:
    import tomli as tomllib  # type: ignore
except ImportError:
    import tomllib  # type: ignore

# Import proof manager from multiplicity_core BEFORE numpy to avoid stub
sys.path.insert(0, str(Path(__file__).parent.parent))
from multiplicity_core.proofs import ProofManager

# Remove local paths that might have stub numpy, then import real numpy
sys.path = [p for p in sys.path if 'atlas-hologram' not in p and p != str(Path(__file__).parent.parent)]

# Detect numpy/cupy backend
backend_env = os.environ.get("AEP_ARRAY_BACKEND", "numpy").lower()
if backend_env == "cupy":
    try:
        import cupy as xp  # type: ignore
    except ImportError:
        import numpy as xp  # type: ignore
        print("Warning: cupy requested but not available, falling back to numpy", file=sys.stderr)
else:
    import numpy as xp  # type: ignore

BASE = Path(__file__).parent.resolve()


def load_kernel() -> tuple[dict[str, Any], dict[str, Any]]:
    """Load aep.toml and kernel.atlas configurations."""
    with open(BASE / "aep.toml", "rb") as f:
        aep = tomllib.load(f)
    with open(BASE / "kernel.atlas", "rb") as f:
        ker = tomllib.load(f)
    return aep, ker


def load_operator(path: Path) -> Any:
    """Load operator matrix from .npy file."""
    return xp.load(str(path))


def check_commutation(M: Any, E: Any, atol: float) -> tuple[bool, float]:
    """
    Compute commutator [M, E_α] = M·E - E·M and check if ||[M,E]|| ≤ atol.
    Returns (ok, norm).
    """
    comm = M @ E - E @ M
    norm = float(xp.linalg.norm(comm))
    return norm <= atol, norm


def read_delta_channels(path: Path) -> dict[str, float]:
    """
    Read Δ-channel data from JSON file.
    Expected format: {"channel_name": value, ...} or [{"name": ..., "norm": ...}, ...]
    """
    if not path.exists():
        return {}
    
    with open(path, "r", encoding="utf-8") as f:
        data = json.load(f)
    
    if isinstance(data, dict):
        return {str(k): float(v) for k, v in data.items()}
    elif isinstance(data, list):
        # Handle list format
        result = {}
        for item in data:
            if isinstance(item, dict) and "name" in item:
                result[str(item["name"])] = float(item.get("norm", 0.0))
        return result
    return {}


def assert_forbidden_zero(delta_map: dict[str, float], patterns: list[str], atol: float) -> tuple[bool, list[str]]:
    """
    Check that all channels matching forbidden patterns have magnitude ≤ atol.
    Returns (ok, violations).
    """
    violations = []
    for name, val in delta_map.items():
        if any(fnmatch.fnmatch(name, pat) for pat in patterns):
            if abs(float(val)) > atol:
                violations.append(f"{name}:{val}")
    return len(violations) == 0, violations


def resonance_delta(aep: dict[str, Any]) -> float | None:
    """
    Optionally compute ||R_post - R_pre|| if resonance evidence is provided.
    Returns norm or None if evidence not available.
    """
    evidence = aep.get("evidence", {})
    pre_cfg = evidence.get("resonance_pre", {})
    post_cfg = evidence.get("resonance_post", {})
    
    if not pre_cfg.get("required", False) and not post_cfg.get("required", False):
        # Try to load if paths exist
        pre_path = BASE / pre_cfg.get("path", "evidence/resonance_pre.npy")
        post_path = BASE / post_cfg.get("path", "evidence/resonance_post.npy")
        
        if pre_path.exists() and post_path.exists():
            R_pre = xp.load(str(pre_path))
            R_post = xp.load(str(post_path))
            delta = R_post - R_pre
            return float(xp.linalg.norm(delta))
    
    return None


def main() -> int:
    aep, ker = load_kernel()
    atol = float(aep.get("constraints", {}).get("atol", 1e-12))

    # Load operators
    M = load_operator(BASE / ker["operators"]["M"])
    E = load_operator(BASE / ker["operators"]["E_alpha"])

    ok_comm, comm_norm = check_commutation(M, E, atol)

    # Check Δ-channels
    channels_cfg = aep.get("evidence", {}).get("channels", {})
    delta_map = read_delta_channels(BASE / channels_cfg.get("path", "evidence/delta_channels.json"))
    patterns = ker.get("probes", {}).get("forbidden_patterns", []) or aep.get("forbidden", {}).get("channels", [])
    ok_delta, delta_viol = assert_forbidden_zero(delta_map, patterns, atol)

    # Optional resonance delta
    res_dn = resonance_delta(aep)

    status = "pass" if (ok_comm and ok_delta) else "fail"

    payload = {
        "aep_id": aep["claim"]["id"],
        "t_ms": int(time.time() * 1000),
        "comm_norm": comm_norm,
        "atol": atol,
        "delta_violations": delta_viol,
        "backend": "cupy" if xp.__name__ == "cupy" else "numpy",
        "res_delta_norm": res_dn,
    }

    proofs = ProofManager()
    p = proofs.generate("ethics_commutation", payload)
    verified = proofs.verify(p, payload)

    out = {
        "status": status,
        "ok_commutation": ok_comm,
        "ok_forbidden_channels": ok_delta,
        "comm_norm": comm_norm,
        "atol": atol,
        "delta_violations": delta_viol,
        "res_delta_norm": res_dn,
        "proof_id": p.proof_id,
        "verified": bool(verified),
    }

    (BASE / "out").mkdir(exist_ok=True)
    with open(BASE / "out/result.json", "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2)

    # Deterministic fail if invariant is broken
    return 0 if status == "pass" and verified else 2


if __name__ == "__main__":
    sys.exit(main())
