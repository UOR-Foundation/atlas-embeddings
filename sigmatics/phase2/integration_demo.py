#!/usr/bin/env python3
"""
Phase 1 + Phase 2 Integration Demonstration

This script demonstrates the complete pipeline:
1. Parse Sigmatics DSL script
2. Lower to deterministic JSON
3. Compile to Multiplicity program (Phase 1)
4. Execute program with trace logging (Phase 2)
5. Evaluate metrics (Phase 2)
"""

import sys
import json
import os
from pathlib import Path

# Add phase1 and phase2 to path
current_dir = Path(__file__).parent
phase1_dir = current_dir.parent / "phase1"
phase2_dir = current_dir
sys.path.insert(0, str(phase1_dir))
sys.path.insert(0, str(phase2_dir))

# Phase 1 imports
from lexer_parser import parse
from lowering import lower
from compiler import compile_program
from policies import Policies

# Phase 2 imports
from executor import run


def print_banner(text):
    """Print a banner."""
    print()
    print("=" * 70)
    print(text)
    print("=" * 70)


def print_section(text):
    """Print a section."""
    print()
    print(text)
    print("-" * 70)


def main():
    """Run the integration demonstration."""
    print_banner("Phase 1 + Phase 2 Integration Demonstration")
    
    # Step 1: Sigmatics Script
    print_section("Step 1: Sigmatics Script")
    
    script = """
mark@{"p":3,"r":1,"mode":"delta"};
rho[17];
copy;
"""
    
    print("Input script:")
    print(script)
    
    # Step 2: Phase 1 - Parse and Lower
    print_section("Step 2: Phase 1 - Parse and Lower")
    
    lowered_data = lower(script, src_name="integration_demo.sig")
    lowered_dict = lowered_data["lowered"]
    lowered_words = lowered_dict["words"]
    lowering_hash = lowered_data["lowering_hash"]
    
    print(f"Lowering hash: {lowering_hash}")
    print(f"Lowered words: {len(lowered_words)}")
    print()
    print("Lowered JSON (first word):")
    print(json.dumps(lowered_words[0], indent=2))
    
    # Step 3: Phase 1 - Compile
    print_section("Step 3: Phase 1 - Compile to Multiplicity")
    
    policies = Policies()
    program = compile_program(lowered_dict, policies)
    
    print(f"Index dimension: n = {program['n']}")
    print(f"Compiled words: {len(program['words'])}")
    print(f"Obligations: {len(program['obligations'])}")
    print()
    print("Compiled words:")
    for i, word in enumerate(program['words'], 1):
        op = word['op']
        details = []
        if op == "projector":
            details.append(f"p={word['p']}, r={word['r']}, mode={word['mode']}")
        elif op == "rotate":
            details.append(f"k={word['k']}")
        if 'note' in word:
            details.append(word['note'])
        print(f"  {i}. {op}", end="")
        if details:
            print(f" ({', '.join(details)})", end="")
        print()
    
    # Step 4: Phase 2 - Execute
    print_section("Step 4: Phase 2 - Execute Program")
    
    outdir = "/tmp/phase1_phase2_integration"
    print(f"Output directory: {outdir}")
    
    metrics = run(program, outdir, seed=42)
    
    print("✓ Execution complete")
    print()
    print("Generated artifacts:")
    for filename in ["program.json", "trace.jsonl", "metrics.json"]:
        path = os.path.join(outdir, filename)
        size = os.path.getsize(path)
        print(f"  • {filename:20} ({size:6,} bytes)")
    
    # Step 5: Phase 2 - Show Results
    print_section("Step 5: Phase 2 - Metrics Summary")
    
    print(f"Signal dimension: n = {metrics['n']}")
    print(f"Modulus used:     m = {metrics['last_m']}")
    print()
    
    print("Energy Explained Ratio (EVR):")
    evr_a = metrics['evr_A']
    evr_d = metrics['evr_Delta']
    baseline_mean = metrics['baseline_evr_A']['mean']
    baseline_std = metrics['baseline_evr_A']['std']
    
    print(f"  A^(m):           {evr_a:.6f}")
    print(f"  Δ_(m):           {evr_d:.6f}")
    print(f"  Sum:             {evr_a + evr_d:.6f}")
    print(f"  Random baseline: {baseline_mean:.6f} ± {baseline_std:.6f}")
    
    # Check if above baseline
    if evr_a > baseline_mean + baseline_std:
        print(f"  → A^(m) is {(evr_a - baseline_mean) / baseline_std:.2f}σ above baseline ✓")
    else:
        print(f"  → A^(m) is near baseline (natural ordering not significant)")
    
    print()
    print("Retrieval Uplift (R²):")
    r2 = metrics['retrieval_uplift']['r2']
    r2_base = metrics['retrieval_uplift']['baseline_mean']
    r2_std = metrics['retrieval_uplift']['baseline_std']
    print(f"  Actual:          {r2:.6f}")
    print(f"  Baseline:        {r2_base:.6f} ± {r2_std:.6f}")
    
    print()
    print("Relation Consistency (Jaccard similarity):")
    rel = metrics['relation_consistency']
    print(f"  Original ∩ Split:  {rel['jaccard_orig_split']:.6f}")
    print(f"  Split ∩ Merge:     {rel['jaccard_split_merge']:.6f}")
    print(f"  Original ∩ Merge:  {rel['jaccard_orig_merge']:.6f}")
    
    # Step 6: Trace Analysis
    print_section("Step 6: Trace Analysis")
    
    trace_path = os.path.join(outdir, "trace.jsonl")
    with open(trace_path, 'r') as f:
        trace_lines = f.readlines()
    
    print(f"Total operations executed: {len(trace_lines)}")
    print()
    
    total_time = 0
    for i, line in enumerate(trace_lines, 1):
        rec = json.loads(line)
        dt = rec['dt_ms']
        total_time += dt
        
        energy_before = rec['pre']['energy']
        energy_after = rec['post']['energy']
        energy_change = energy_after - energy_before
        
        print(f"Op {i}: {rec['op']:15} | ", end="")
        print(f"ΔE = {energy_change:+10.2f} | ", end="")
        print(f"time = {dt:3} ms")
    
    print()
    print(f"Total execution time: {total_time} ms")
    
    # Step 7: Verification
    print_section("Step 7: Verification")
    
    print("✓ Phase 1: Compilation successful")
    print(f"  - Parsed {len(lowered_words)} Sigmatics words")
    print(f"  - Generated {len(program['words'])} Multiplicity words")
    print(f"  - Tracked {len(program['obligations'])} obligations")
    
    print()
    print("✓ Phase 2: Execution successful")
    print(f"  - Executed {len(trace_lines)} operations")
    print(f"  - Computed {len([k for k in metrics if k not in ['n', 'last_m']])} metric types")
    print(f"  - Generated 3 artifact files")
    
    print()
    print("✓ Integration: Pipeline complete")
    print(f"  - DSL → JSON → Multiplicity → Execution → Metrics")
    
    # Final summary
    print_banner("Pipeline Summary")
    print()
    print("  Input:  Sigmatics DSL script")
    print(f"  Output: Artifacts in {outdir}/")
    print()
    print("  Pipeline stages:")
    print("    1. Parse   → Deterministic lowering")
    print("    2. Compile → Π-first reduction")
    print("    3. Execute → Signal + relation paths")
    print("    4. Evaluate → Resonance metrics")
    print()
    print("  Status: ✓ All stages completed successfully")
    print()
    print("=" * 70)


if __name__ == "__main__":
    main()
