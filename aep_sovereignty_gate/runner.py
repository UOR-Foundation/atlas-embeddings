#!/usr/bin/env python3
"""
Sovereignty Gate AEP Runner

Validates:
1. Σ_i(t) == 1 for acting identity (via plugin or allowlist)
2. All forbidden Δ-channels have magnitude ≤ atol
3. Generates deterministic proof and verifies it
4. Exits 0 on pass, 2 on invariant violation, 3 on missing actor_id, 4 on plugin error
"""
from __future__ import annotations

import fnmatch
import importlib.util
import json
import os
import sys
import time
from pathlib import Path
from typing import Any, Callable

try:
    import tomli as tomllib  # type: ignore
except ImportError:
    import tomllib  # type: ignore

# Import proof manager from multiplicity_core
sys.path.insert(0, str(Path(__file__).parent.parent))
from multiplicity_core.proofs import ProofManager

BASE = Path(__file__).parent.resolve()


def load_kernel() -> tuple[dict[str, Any], dict[str, Any]]:
    """Load aep.toml and kernel.atlas configurations."""
    with open(BASE / "aep.toml", "rb") as f:
        aep = tomllib.load(f)
    with open(BASE / "kernel.atlas", "rb") as f:
        ker = tomllib.load(f)
    return aep, ker


def import_sigma(plugin_path: str | None) -> Callable[[str, int], int] | None:
    """
    Dynamically import sigma function from plugin if provided.
    Expected signature: sigma(actor_id: str, t_ms: int) -> int
    """
    if not plugin_path:
        return None
    
    full_path = BASE / plugin_path
    if not full_path.exists():
        return None
    
    spec = importlib.util.spec_from_file_location("sigma_plugin", full_path)
    if spec is None or spec.loader is None:
        return None
    
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    
    if hasattr(module, "sigma"):
        return module.sigma  # type: ignore
    
    return None


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


def main() -> int:
    aep, ker = load_kernel()
    actor_env = os.environ.get("AEP_ACTOR_ID", "").strip()
    actor_cfg = ker.get("context", {}).get("actor_id", "").strip()
    actor_id = actor_env or actor_cfg
    if not actor_id:
        print("missing actor_id (env AEP_ACTOR_ID or kernel.context.actor_id)", file=sys.stderr)
        return 3

    policy = aep.get("policy", {})
    sigma_fn = import_sigma(policy.get("sigma_plugin"))
    allowed_ids = policy.get("allowed_ids", [])

    t_ms = int(time.time() * 1000)

    if sigma_fn is not None:
        try:
            s_val = int(sigma_fn(actor_id, t_ms))
        except Exception as e:
            print(f"sigma plugin error: {e}", file=sys.stderr)
            return 4
    else:
        s_val = 1 if actor_id in allowed_ids else 0

    ok_sigma = (s_val == 1)

    # Check Δ-channels
    channels_cfg = aep.get("evidence", {}).get("channels", {})
    delta_map = read_delta_channels(BASE / channels_cfg.get("path", "evidence/delta_channels.json"))
    patterns = ker.get("probes", {}).get("forbidden_patterns", []) or aep.get("forbidden", {}).get("channels", [])
    atol = float(aep.get("constraints", {}).get("atol", 1e-12)) if "constraints" in aep else 1e-12
    ok_delta, delta_viol = assert_forbidden_zero(delta_map, patterns, atol)

    status = "pass" if (ok_sigma and ok_delta) else "fail"

    payload = {
        "aep_id": aep["claim"]["id"],
        "t_ms": t_ms,
        "actor_id": actor_id,
        "sigma": s_val,
        "delta_violations": delta_viol,
    }

    proofs = ProofManager()
    p = proofs.generate("sovereignty_gate", payload)
    verified = proofs.verify(p, payload)

    out = {
        "status": status,
        "ok_sigma": ok_sigma,
        "ok_forbidden_channels": ok_delta,
        "sigma": s_val,
        "actor_id": actor_id,
        "delta_violations": delta_viol,
        "proof_id": p.proof_id,
        "verified": bool(verified),
    }

    (BASE / "out").mkdir(exist_ok=True)
    with open(BASE / "out/result.json", "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2)

    return 0 if status == "pass" and verified else 2


if __name__ == "__main__":
    sys.exit(main())
