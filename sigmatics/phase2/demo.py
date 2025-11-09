#!/usr/bin/env python3
"""
Phase 2 Demonstration

This script demonstrates the full Phase 1 → Phase 2 pipeline:
1. Load or create a compiled program from Phase 1
2. Execute the program with the Phase 2 executor
3. Generate trace and metrics
4. Display summary results
"""

import sys
import json
import os
from pathlib import Path

# Add phase1 and phase2 to path
phase2_dir = Path(__file__).parent
phase1_dir = phase2_dir.parent / "phase1"
sys.path.insert(0, str(phase1_dir))
sys.path.insert(0, str(phase2_dir))

from executor import run, N


def create_example_program():
    """Create a simple example program for demonstration."""
    return {
        "n": N,
        "words": [
            {"op": "projector", "p": 3, "r": 1, "mode": "Δ", "note": "Phase 1 compiled"},
            {"op": "rotate", "k": 17},
            {"op": "copy"},
            {"op": "permute", "note": "UNPROVEN permPolicy"},
            {"op": "split", "ellType": "int"},
            {"op": "merge"},
            {"op": "modal_enter"},
            {"op": "rotate", "k": -17},  # Mirror approximation
            {"op": "modal_exit"},
            {"op": "permute", "note": "UNPROVEN permPolicy"},
        ],
        "obligations": [
            {"type": "policy", "name": "primePolicy/levelPolicy/markMode", "status": "UNPROVEN"},
            {"type": "policy", "name": "permPolicy", "status": "UNPROVEN"},
            {"type": "policy", "name": "arityPolicy", "status": "UNPROVEN"},
            {"type": "semantics", "name": "quote", "status": "UNPROVEN"},
            {"type": "policy", "name": "permPolicy", "status": "UNPROVEN"},
            {"type": "semantics", "name": "evaluate", "status": "UNPROVEN"},
            {"type": "policy", "name": "permPolicy", "status": "UNPROVEN"},
        ]
    }


def print_section(title):
    """Print a section header."""
    print()
    print("=" * 70)
    print(title)
    print("=" * 70)


def print_subsection(title):
    """Print a subsection header."""
    print()
    print("-" * 70)
    print(title)
    print("-" * 70)


def main():
    """Run the Phase 2 demonstration."""
    print_section("Phase 2 — Executor and Evaluator Demonstration")
    
    # 1. Create or load program
    print_subsection("1. Example Program (from Phase 1)")
    program = create_example_program()
    
    print(f"Index dimension: n = {program['n']}")
    print(f"Operations: {len(program['words'])}")
    print(f"Obligations: {len(program['obligations'])}")
    print()
    print("Operations:")
    for i, w in enumerate(program['words'], 1):
        op = w['op']
        note = f" — {w['note']}" if 'note' in w else ""
        details = ""
        if op == "projector":
            details = f" (p={w['p']}, r={w['r']}, mode={w['mode']})"
        elif op == "rotate":
            details = f" (k={w['k']})"
        elif op == "split":
            details = f" (type={w.get('ellType', 'unknown')})"
        print(f"  {i:2}. {op}{details}{note}")
    
    # 2. Execute program
    print_subsection("2. Executing Program")
    outdir = "/tmp/phase2_demo"
    print(f"Output directory: {outdir}")
    print("Running executor...")
    
    metrics = run(program, outdir, seed=42)
    
    print("✓ Execution complete")
    
    # 3. Show artifacts
    print_subsection("3. Generated Artifacts")
    artifacts = ["program.json", "trace.jsonl", "metrics.json"]
    for artifact in artifacts:
        path = os.path.join(outdir, artifact)
        if os.path.exists(path):
            size = os.path.getsize(path)
            print(f"  ✓ {artifact:20} ({size:7,} bytes)")
        else:
            print(f"  ✗ {artifact:20} (missing)")
    
    # 4. Show trace sample
    print_subsection("4. Trace Sample (first 3 operations)")
    trace_path = os.path.join(outdir, "trace.jsonl")
    with open(trace_path, 'r') as f:
        lines = f.readlines()[:3]
        for i, line in enumerate(lines, 1):
            rec = json.loads(line)
            print(f"\n  Operation {i}: {rec['op']}")
            print(f"    Pre-energy:  {rec['pre']['energy']:12.2f}")
            print(f"    Post-energy: {rec['post']['energy']:12.2f}")
            print(f"    Time:        {rec['dt_ms']:12} ms")
            if 'mark' in rec:
                mark = rec['mark']
                print(f"    Projector:   p={mark['p']}, r={mark['r']}, m={mark['m']}, mode={mark['mode']}")
    
    # 5. Show metrics
    print_subsection("5. Evaluation Metrics")
    
    print(f"\n  Signal dimension: n = {metrics['n']}")
    print(f"  Last modulus:     m = {metrics['last_m']}")
    
    print(f"\n  Energy Explained Ratio (EVR):")
    print(f"    A^(m):     {metrics['evr_A']:.6f}")
    print(f"    Δ_(m):     {metrics['evr_Delta']:.6f}")
    print(f"    Baseline:  {metrics['baseline_evr_A']['mean']:.6f} ± {metrics['baseline_evr_A']['std']:.6f}")
    
    uplift = metrics['retrieval_uplift']
    print(f"\n  Retrieval Uplift (R²):")
    print(f"    Actual:    {uplift['r2']:.6f}")
    print(f"    Baseline:  {uplift['baseline_mean']:.6f} ± {uplift['baseline_std']:.6f}")
    
    rel = metrics['relation_consistency']
    print(f"\n  Relation Consistency (Jaccard):")
    print(f"    Original ∩ Split:  {rel['jaccard_orig_split']:.6f}")
    print(f"    Split ∩ Merge:     {rel['jaccard_split_merge']:.6f}")
    print(f"    Original ∩ Merge:  {rel['jaccard_orig_merge']:.6f}")
    print(f"    Edge counts:       |E0|={int(rel['|E0|'])}, |Es|={int(rel['|Es|'])}, |Em|={int(rel['|Em|'])}")
    
    # 6. Summary
    print_section("Summary")
    print(f"  ✓ Executed {len(program['words'])} operations")
    print(f"  ✓ Generated {len(lines)} trace entries")
    print(f"  ✓ Computed {len([k for k in metrics.keys() if k not in ['n', 'last_m']])} metric categories")
    print(f"  ✓ Tracked {len(program['obligations'])} UNPROVEN obligations")
    print()
    print(f"  Artifacts saved to: {outdir}")
    print()
    print("=" * 70)
    print()


if __name__ == "__main__":
    main()
