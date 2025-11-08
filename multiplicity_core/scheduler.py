"""
Schedule executor for ACE: reads atlas_schedule.toml and round-robins through slots.
Calls ACE per slot and emits PETC stamps. On fail, logs ace_reject and continues.

Contract: supply proposal(c,a,k)->(T_t,F,K_prop,w,eps) and writeback(c,a,k,T_next).
"""
from __future__ import annotations

# Fix numpy import conflict with local stub
import sys
import os
_repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
_original_path = sys.path.copy()
sys.path = [p for p in sys.path if p != _repo_root and not p.endswith('/atlas-hologram')]
try:
    import numpy as _real_np
finally:
    sys.path = _original_path
# Now inject real numpy into sys.modules
sys.modules['numpy'] = _real_np
np = _real_np

import argparse
import json
import time
from pathlib import Path
from typing import Any, Callable, Dict, Optional

try:
    import tomli as toml_load  # type: ignore
except ImportError:
    try:
        import tomllib as toml_load  # type: ignore (Python 3.11+)
    except ImportError:
        import toml as toml_load  # type: ignore


from multiplicity_core.ace_runtime_xp import ACEConfigXP, ACERuntimeXP, FailClosed
from multiplicity_core.ledger import Ledger


def load_schedule(path: str) -> Dict[str, Any]:
    """Load schedule configuration from TOML file."""
    p = Path(path)
    if not p.exists():
        raise FileNotFoundError(f"Schedule file not found: {path}")
    
    with open(p, "rb") as f:
        return toml_load.load(f)


def executor(
    ledger: Ledger,
    schedule_cfg: Dict[str, Any],
    proposal: Callable,
    writeback: Callable,
    steps: int = 1024,
    backend: str = "numpy",
) -> None:
    """Execute scheduled ACE steps.
    
    Args:
        ledger: Ledger for recording events
        schedule_cfg: Schedule configuration dict
        proposal: Callable(c, a, k) -> (T_t, F, K_prop, w, eps)
        writeback: Callable(c, a, k, T_next) -> None
        steps: Number of steps to execute
        backend: "numpy" or "cupy"
    """
    # Extract schedule parameters
    n_classes = schedule_cfg.get("n_classes", 12)
    n_anchors = schedule_cfg.get("n_anchors", 6)
    n_columns = schedule_cfg.get("n_columns", 768)
    
    # ACE config from schedule
    ace_cfg = ACEConfigXP(
        lam_l1=schedule_cfg.get("lam_l1", 0.1),
        l1_weight_floor=schedule_cfg.get("l1_weight_floor", 1e-6),
        kkt_tol=schedule_cfg.get("kkt_tol", 1e-6),
    )
    
    # Initialize ACE runtime
    ace = ACERuntimeXP(ledger, cfg=ace_cfg, backend=backend, return_numpy=True)
    
    # Round-robin through slots
    for step in range(steps):
        c = step % n_classes
        a = (step // n_classes) % n_anchors
        k = (step // (n_classes * n_anchors)) % n_columns
        
        # Get proposal
        T_t, F, K_prop, w, eps = proposal(c, a, k)
        
        # Emit PETC stamp
        petc_entry = {
            "kind": "petc_stamp",
            "step": step,
            "class": c,
            "anchor": a,
            "column": k,
            "ts_ms": int(time.time() * 1000),
        }
        ledger.append(petc_entry)
        
        # Execute ACE step
        try:
            result = ace.ace_step(
                T_t=T_t,
                F=F,
                K_prop=K_prop,
                w_l1=w,
                eps_t=eps,
                actor_id=f"slot_{c}_{a}_{k}",
                context={"step": step, "class": c, "anchor": a, "column": k},
            )
            # Writeback
            writeback(c, a, k, result["T_next"])
            
        except FailClosed as e:
            # Log rejection and continue
            reject_entry = {
                "kind": "ace_reject",
                "step": step,
                "class": c,
                "anchor": a,
                "column": k,
                "error": str(e),
                "ts_ms": int(time.time() * 1000),
            }
            ledger.append(reject_entry)


def demo_proposal_factory(d: int = 256):
    """Demo proposal and writeback factory.
    
    Args:
        d: Dimension of state vector
    
    Returns:
        Tuple of (proposal, writeback) functions
    """
    # Trivial state: single vector T
    scale = 0.01
    state = {
        "T": np.zeros((d,)),
    }

    def proposal(c: int, a: int, k: int):
        T_t = state["T"]
        F = np.zeros_like(T_t)
        K_prop = scale * np.eye(d)
        w = np.ones_like(T_t)
        eps = 0.01
        return T_t, F, K_prop, w, eps

    def writeback(c: int, a: int, k: int, T_next):
        state["T"] = T_next

    return proposal, writeback


def main():
    """Main entry point for scheduler."""
    ap = argparse.ArgumentParser()
    ap.add_argument("--schedule", default="atlas_schedule.toml")
    ap.add_argument("--steps", type=int, default=1024)
    ap.add_argument("--backend", choices=["numpy", "cupy"], default="numpy")
    args = ap.parse_args()

    schedule_cfg = load_schedule(args.schedule)
    ledger = Ledger()

    proposal, writeback = demo_proposal_factory(d=256)
    executor(
        ledger, schedule_cfg, proposal, writeback, steps=args.steps, backend=args.backend
    )

    print("ledger tail:")
    for ent in ledger.entries[-10:]:
        print(json.dumps(ent, indent=2))


if __name__ == "__main__":
    main()
