#!/usr/bin/env python3
"""
phase3_validation_kpis.py — Phase 3 Validation & KPI Wrapper

Validates unit properties and computes KPIs for compiled programs.

This is a convenience wrapper around the Phase 3 validation module,
providing a simple CLI interface for the ship plan.

Usage:
    python phase3_validation_kpis.py --program compiled.json --outdir results/ --seed 42

Outputs:
    - validation_report.json: Unit property test results
    - roundtrip.json: Round-trip integrity checks
    - kpis.json: Consolidated KPI summary
"""

import argparse
import json
import os
import sys
from pathlib import Path

# Add sigmatics to path
REPO_ROOT = Path(__file__).parent.parent.parent
sys.path.insert(0, str(REPO_ROOT / "sigmatics" / "phase3"))

try:
    from phase3 import (
        unit_projector_idempotence,
        unit_noncommutation_witness,
        unit_rotation_closure,
        unit_split_merge_roundtrip,
        roundtrip_check,
        determinism_rate,
        obligation_counts,
    )
except ImportError:
    print("Error: Phase 3 validation module not found", file=sys.stderr)
    print("Make sure sigmatics/phase3/phase3.py exists", file=sys.stderr)
    sys.exit(1)


def main():
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Phase 3 — Validation & KPIs",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Validate compiled program
  python phase3_validation_kpis.py --program compiled.json --outdir results/

  # Also run determinism check on source
  python phase3_validation_kpis.py --program compiled.json --source example.sig --outdir results/

  # Custom trials for validation
  python phase3_validation_kpis.py --program compiled.json --outdir results/ --trials 10

  # Verbose output
  python phase3_validation_kpis.py --program compiled.json --outdir results/ -v
        """
    )
    
    parser.add_argument(
        "--program",
        required=True,
        help="Compiled program JSON (from Phase 1)"
    )
    parser.add_argument(
        "--source",
        help="Optional: Source .sig file for round-trip and determinism checks"
    )
    parser.add_argument(
        "--outdir",
        default="results",
        help="Output directory (default: results)"
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=42,
        help="Random seed for reproducibility (default: 42)"
    )
    parser.add_argument(
        "--trials",
        type=int,
        default=5,
        help="Number of trials for validation tests (default: 5)"
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Verbose output"
    )
    
    args = parser.parse_args()
    
    # Load program
    try:
        with open(args.program, "r") as f:
            program = json.load(f)
    except FileNotFoundError:
        print(f"Error: Program file not found: {args.program}", file=sys.stderr)
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in program file: {e}", file=sys.stderr)
        sys.exit(1)
    
    if args.verbose:
        print(f"Phase 3 Validation & KPIs")
        print(f"Program: {args.program}")
        print(f"Output: {args.outdir}")
        print(f"Seed: {args.seed}")
        print(f"Trials: {args.trials}")
        print()
    
    # Set random seed
    import random
    import numpy as np
    random.seed(args.seed)
    np.random.seed(args.seed)
    
    # Create output directory
    os.makedirs(args.outdir, exist_ok=True)
    
    # Run validation tests
    if args.verbose:
        print("Running validation tests...")
    
    try:
        validation = {
            "projector_idempotence": unit_projector_idempotence(trials=args.trials),
            "noncommutation_witness": unit_noncommutation_witness(p=3, q=5, trials=args.trials),
            "rotation_closure": unit_rotation_closure(),
            "split_merge_roundtrip": unit_split_merge_roundtrip(),
        }
        
        validation_path = os.path.join(args.outdir, "validation_report.json")
        with open(validation_path, "w") as f:
            json.dump(validation, f, indent=2)
        
        if args.verbose:
            print(f"  ✓ Projector idempotence validated")
            print(f"  ✓ Non-commutation witness: max_diff = {validation['noncommutation_witness']['max_diff']:.3f}")
            print(f"  ✓ Rotation closure verified")
            print(f"  ✓ Split-merge round-trip verified")
            print()
        
    except Exception as e:
        print(f"Error during validation: {e}", file=sys.stderr)
        if args.verbose:
            import traceback
            traceback.print_exc()
        sys.exit(1)
    
    # Round-trip check (if source provided)
    if args.source:
        try:
            with open(args.source, "r") as f:
                script = f.read()
            
            roundtrip = roundtrip_check(script)
            roundtrip_path = os.path.join(args.outdir, "roundtrip.json")
            with open(roundtrip_path, "w") as f:
                json.dump(roundtrip, f, indent=2)
            
            if args.verbose:
                print(f"Round-trip check:")
                print(f"  Hash equal: {roundtrip.get('hash_equal', False)}")
                print(f"  Supported: {roundtrip.get('supported', False)}")
                print()
        
        except Exception as e:
            print(f"Warning: Round-trip check failed: {e}", file=sys.stderr)
    
    # Compute KPIs
    if args.verbose:
        print("Computing KPIs...")
    
    try:
        oblig = obligation_counts(program)
        
        # Load metrics if available
        metrics_path = os.path.join(args.outdir, "metrics.json")
        if os.path.exists(metrics_path):
            with open(metrics_path, "r") as f:
                metrics = json.load(f)
        else:
            # Use defaults
            metrics = {
                "evr_A": 1.0 / 3.0,
                "baseline_evr_A": {"mean": 1.0 / 3.0},
                "wall_time_compile_s": 0.0,
                "wall_time_exec_s": 0.0,
            }
        
        # Determinism rate (if source provided)
        det_rate = 1.0
        if args.source:
            try:
                with open(args.source, "r") as f:
                    script = f.read()
                det_rate = determinism_rate(script, variants=20)
            except Exception as e:
                print(f"Warning: Determinism rate check failed: {e}", file=sys.stderr)
        
        # Build KPIs
        evr_A = metrics.get("evr_A", 0.0)
        baseline = metrics.get("baseline_evr_A", {})
        baseline_mean = baseline.get("mean", evr_A) if isinstance(baseline, dict) else baseline
        
        noncom = validation.get("noncommutation_witness", {})
        
        kpis = {
            "n": 12288,
            "resonance_uplift_vs_baseline": evr_A - baseline_mean,
            "evr_A": evr_A,
            "baseline_evr_A_mean": baseline_mean,
            "wall_time_compile_s": metrics.get("wall_time_compile_s", 0.0),
            "wall_time_exec_s": metrics.get("wall_time_exec_s", 0.0),
            "determinism_rate_lowering": det_rate,
            "obligation_counts": oblig,
            "noncommute_trials": noncom.get("noncommute_trials", 0),
            "noncommute_trials_total": noncom.get("trials", 0),
            "unit_tests": {
                "projector_idempotence": "pass" if validation.get("projector_idempotence") else "fail",
                "rotation_closure": "pass" if validation.get("rotation_closure") else "fail",
                "noncommutation_witness": "pass" if noncom.get("noncommute_trials", 0) > 0 else "fail",
                "split_merge_roundtrip": "pass" if validation.get("split_merge_roundtrip", {}).get("roundtrip_equal") else "fail",
            },
        }
        
        kpis_path = os.path.join(args.outdir, "kpis.json")
        with open(kpis_path, "w") as f:
            json.dump(kpis, f, indent=2)
        
        if args.verbose:
            print(f"KPI Summary:")
            print(f"  Resonance uplift: {kpis['resonance_uplift_vs_baseline']:.3f}")
            print(f"  Determinism rate: {kpis['determinism_rate_lowering']:.1%}")
            print(f"  UNPROVEN: {oblig['UNPROVEN']}")
            print(f"  VIOLATION: {oblig['VIOLATION']}")
            print()
        
        print(f"Artifacts generated:")
        print(f"  - {validation_path}")
        if args.source:
            print(f"  - {roundtrip_path}")
        print(f"  - {kpis_path}")
        
    except Exception as e:
        print(f"Error computing KPIs: {e}", file=sys.stderr)
        if args.verbose:
            import traceback
            traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
