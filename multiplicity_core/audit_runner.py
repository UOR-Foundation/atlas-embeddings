"""
Audit Runner — check fairness, PETC compliance, and audit interval coverage.

Validates a ledger dump against a schedule and audit policy:
- Class and anchor fairness (round-robin distribution)
- PETC-per-step presence (every ace_step has a corresponding petc)
- Audit interval compliance (audit entries at expected frequencies)
"""
from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path
from typing import Dict, List, Any

try:
    import tomli as toml_load  # type: ignore
except ImportError:
    try:
        import tomllib as toml_load  # type: ignore (Python 3.11+)
    except ImportError:
        import toml as toml_load  # type: ignore


def load_toml(path: str) -> Dict[str, Any]:
    """Load TOML configuration file."""
    p = Path(path)
    if not p.exists():
        raise FileNotFoundError(f"File not found: {path}")
    
    with open(p, "rb") as f:
        return toml_load.load(f)


def load_ledger(path: str) -> List[Dict[str, Any]]:
    """Load ledger JSON file (list of entries)."""
    p = Path(path)
    if not p.exists():
        raise FileNotFoundError(f"Ledger not found: {path}")
    
    with open(p, "r") as f:
        data = json.load(f)
    
    # Handle both list format and dict with 'entries' key
    if isinstance(data, list):
        return data
    elif isinstance(data, dict) and "entries" in data:
        return data["entries"]
    else:
        raise ValueError("Ledger must be a list or dict with 'entries' key")


def audit(
    ledger: List[Dict[str, Any]],
    schedule: Dict[str, Any],
    bundle: Dict[str, Any]
) -> Dict[str, Any]:
    """Audit ledger entries against schedule and policy.
    
    Args:
        ledger: List of ledger entries
        schedule: Schedule configuration
        bundle: Audit policy bundle
    
    Returns:
        Audit report with fairness and compliance checks
    """
    # Extract config
    policy = bundle.get("policy", {})
    intervals = bundle.get("intervals", {})
    required = bundle.get("required_kinds", {})
    indexing = bundle.get("indexing", {})
    
    tol_c = policy.get("class_skew_tolerance", 1)
    tol_a = policy.get("anchor_skew_tolerance", 1)
    audit_every = intervals.get("audit_every", 768)
    
    classes = indexing.get("classes", schedule.get("n_classes", 96))
    anchors = indexing.get("anchors", schedule.get("n_anchors", 6))
    
    # Filter to committed/accepted entries
    entries = [e for e in ledger if e.get("status") in ("committed", "accepted", None)]
    
    # Count total steps
    ace_steps = [e for e in entries if e.get("kind") == "ace_step"]
    n = len(ace_steps)
    
    if n == 0:
        return {
            "total_steps": 0,
            "error": "No ace_step entries found in ledger"
        }
    
    # Count by class and anchor
    by_class: Dict[int, int] = defaultdict(int)
    by_anchor: Dict[int, int] = defaultdict(int)
    
    for e in ace_steps:
        ctx = e.get("context", {})
        if "class" in ctx:
            by_class[int(ctx["class"])] += 1
        if "anchor" in ctx:
            by_anchor[int(ctx["anchor"])] += 1
    
    # Check fairness
    # Classes
    exp_c = n // classes
    bad_classes = {c: cnt for c, cnt in by_class.items() if abs(cnt - exp_c) > tol_c}
    
    # Anchors
    exp_a = n // anchors
    bad_anchors = {a: cnt for a, cnt in by_anchor.items() if abs(cnt - exp_a) > tol_a}
    
    # Per-step requirements: after each accepted step t, a PETC referencing it must exist
    ace_to_petc: Dict[str, int] = defaultdict(int)
    for e in entries:
        if e.get("kind") == "petc":
            ctx = e.get("context", {})
            ref = ctx.get("ace")
            if ref:
                ace_to_petc[ref] += 1
    
    missing_petc = []
    for e in entries:
        if e.get("kind") == "ace_step" and e.get("status") == "committed":
            eid = e.get("entry_id")
            if ace_to_petc.get(eid, 0) == 0:
                missing_petc.append(eid)
    
    # Audit interval presence
    audit_hits = [e for e in entries if e.get("kind") == "audit"]
    audit_ok = True
    if audit_every:
        seen = set([x.get("t") for x in audit_hits])
        # check latest step produces integer multiples up to n
        for k in range(audit_every, n + 1, audit_every):
            if k not in seen:
                audit_ok = False
                break
    
    return {
        "total_steps": n,
        "by_class": dict(by_class),
        "by_anchor": dict(by_anchor),
        "fair_classes_ok": len(bad_classes) == 0,
        "fair_anchors_ok": len(bad_anchors) == 0,
        "bad_classes": bad_classes,
        "bad_anchors": bad_anchors,
        "missing_petc": missing_petc,
        "audit_entries": len(audit_hits),
        "audit_ok": audit_ok,
    }


def main():
    """Main CLI entry point."""
    ap = argparse.ArgumentParser(
        description="Audit ACE runtime ledger for fairness and compliance"
    )
    ap.add_argument("--schedule", default="atlas_schedule.toml", 
                    help="Schedule configuration file")
    ap.add_argument("--bundle", default="audit_bundle.toml",
                    help="Audit policy bundle file")
    ap.add_argument("--ledger", required=True,
                    help="Ledger JSON file to audit")
    args = ap.parse_args()
    
    sched = load_toml(args.schedule)
    bund = load_toml(args.bundle)
    ledg = load_ledger(args.ledger)
    report = audit(ledg, sched, bund)
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
