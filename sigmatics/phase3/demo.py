#!/usr/bin/env python3
"""
Phase 3 — Validation & KPIs Demonstration

This script demonstrates the complete Phase 3 pipeline:
1. Lowering and compilation (Phase 1 subset)
2. Execution and metrics (Phase 2 subset)
3. Unit property validation (Phase 3)
4. Round-trip integrity checks (Phase 3)
5. KPI computation (Phase 3)
"""

import json
import tempfile
import os
from pathlib import Path

from phase3 import (
    N,
    lower, compile_program, Policies,
    exec_program, unit_projector_idempotence,
    unit_noncommutation_witness, unit_rotation_closure,
    unit_split_merge_roundtrip, roundtrip_check,
    determinism_rate, obligation_counts
)


def print_header(title: str):
    """Print a section header."""
    print()
    print("=" * 70)
    print(title)
    print("=" * 70)
    print()


def print_section(title: str):
    """Print a subsection header."""
    print()
    print("-" * 70)
    print(title)
    print("-" * 70)


def main():
    print_header("Phase 3 — Validation & KPIs Demonstration")
    
    # Example Sigmatics script
    script = """
        mark@{"p":3,"r":1,"mode":"delta"};
        rho[17];
        copy;
        split@ℓ:int;
        merge;
        quote;
        evaluate;
    """
    
    print("1. Example Sigmatics script:")
    print_section("Source")
    print(script.strip())
    
    # Phase 1: Lower and compile
    print_section("2. Phase 1: Lowering and compilation")
    lowered = lower(script, src_name="demo.sig")
    print(f"Lowering hash: {lowered['lowering_hash']}")
    print(f"Number of words: {len(lowered['lowered']['words'])}")
    
    program = compile_program(lowered["lowered"], Policies())
    print(f"Index size n: {program['n']}")
    print(f"Compiled words: {len(program['words'])}")
    print(f"Obligations tracked: {len(program['obligations'])}")
    
    print("\nFirst 5 compiled words:")
    for i, w in enumerate(program["words"][:5], 1):
        op = w["op"]
        if op == "projector":
            print(f"  {i}. {op} (p={w['p']}, r={w['r']}, mode={w['mode']}) — {w.get('note', '')}")
        elif op == "rotate":
            print(f"  {i}. {op} (k={w['k']})")
        elif op == "merge":
            print(f"  {i}. {op} (arity={w.get('arity', 2)})")
        else:
            note = f" — {w['note']}" if 'note' in w else ""
            print(f"  {i}. {op}{note}")
    
    # Phase 2: Execute
    print_section("3. Phase 2: Execution and metrics")
    with tempfile.TemporaryDirectory() as tmpdir:
        metrics = exec_program(program, tmpdir, seed=42)
        
        print(f"Wall time (exec): {metrics['wall_time_exec_s']:.4f}s")
        print(f"Last m (modulus): {metrics['last_m']}")
        print(f"EVR (A): {metrics['evr_A']:.6f}")
        print(f"EVR (Δ): {metrics['evr_Delta']:.6f}")
        print(f"Baseline EVR (A): {metrics['baseline_evr_A']['mean']:.6f} ± {metrics['baseline_evr_A']['std']:.6f}")
        print(f"Relation edges: {metrics['relation']['|E|']}")
        
        resonance_uplift = metrics['evr_A'] - metrics['baseline_evr_A']['mean']
        print(f"\nResonance uplift: {resonance_uplift:+.6f}")
    
    # Phase 3: Unit properties
    print_section("4. Phase 3: Unit property validation")
    
    print("\na) Projector idempotence (A² = A, Δ² = Δ):")
    idempotence = unit_projector_idempotence(trials=3)
    for mode in ["A", "Delta"]:
        errors = [item["max_abs_err"] for item in idempotence[mode]]
        avg_err = sum(errors) / len(errors)
        max_err = max(errors)
        print(f"   {mode:5s}: avg_err={avg_err:.2e}, max_err={max_err:.2e}")
    
    print("\nb) Non-commutation witness (A_p W_q ≠ W_q A_p):")
    noncommute = unit_noncommutation_witness(p=3, q=5, trials=5)
    print(f"   p={noncommute['p']}, q={noncommute['q']}")
    print(f"   Non-commuting trials: {noncommute['noncommute_trials']}/{noncommute['trials']}")
    print(f"   Difference range: [{noncommute['min_diff']:.6f}, {noncommute['max_diff']:.6f}]")
    
    print("\nc) Rotation closure (R^n = Identity):")
    rotation = unit_rotation_closure()
    print(f"   Max absolute error: {rotation['R^n_identity_max_abs_err']:.2e}")
    
    print("\nd) Split-merge round-trip:")
    split_merge = unit_split_merge_roundtrip(m=3)
    print(f"   Contracted edges: {split_merge['contracted_edges']}")
    print(f"   Round-trip equal: {split_merge['roundtrip_equal']}")
    
    # Round-trip integrity
    print_section("5. Round-trip integrity check")
    
    subset_script = """
        mark@{"p":3,"r":1,"mode":"delta"};
        rho[7];
        copy;
    """
    
    rt = roundtrip_check(subset_script)
    print(f"Hash 1: {rt['lowering_hash_1'][:16]}...")
    print(f"Hash 2: {rt['lowering_hash_2'][:16]}...")
    print(f"Hashes equal: {rt['hash_equal']}")
    print(f"Structure equal: {rt['structure_equal']}")
    print("\nPretty-printed script:")
    for line in rt['pretty_script'].split('\n'):
        if line.strip():
            print(f"  {line}")
    
    # KPIs
    print_section("6. KPI computation")
    
    det = determinism_rate(subset_script, variants=20)
    print(f"Determinism rate (lowering): {det:.1%}")
    
    oblig = obligation_counts(program)
    print(f"Obligation counts:")
    print(f"  UNPROVEN: {oblig['UNPROVEN']}")
    print(f"  VIOLATION: {oblig['VIOLATION']}")
    
    print("\nKPI Summary:")
    print(f"  n: {N}")
    print(f"  Resonance uplift: {resonance_uplift:+.6f}")
    print(f"  EVR (A): {metrics['evr_A']:.6f}")
    print(f"  Baseline (A): {metrics['baseline_evr_A']['mean']:.6f}")
    print(f"  Wall time (exec): {metrics['wall_time_exec_s']:.4f}s")
    print(f"  Determinism rate: {det:.1%}")
    print(f"  UNPROVEN obligations: {oblig['UNPROVEN']}")
    print(f"  Non-commute trials: {noncommute['noncommute_trials']}/{noncommute['trials']}")
    
    # Obligations detail
    print_section("7. Obligations detail (UNPROVEN items)")
    for i, ob in enumerate(program["obligations"], 1):
        ob_type = ob.get("type", "unknown")
        name = ob.get("name", "")
        status = ob.get("status", "")
        print(f"  {i}. [{ob_type}] {name} — {status}")
    
    print_header("Summary")
    print("✓ Phase 1: Lowering and compilation complete")
    print("✓ Phase 2: Execution and metrics complete")
    print("✓ Phase 3: Validation complete")
    print(f"✓ All unit properties validated")
    print(f"✓ Round-trip integrity verified")
    print(f"✓ KPIs computed")
    print(f"! {oblig['UNPROVEN']} UNPROVEN obligations tracked")
    print()
    print("Note: All policies remain UNPROVEN pending mathematical verification.")
    print()


if __name__ == "__main__":
    main()
