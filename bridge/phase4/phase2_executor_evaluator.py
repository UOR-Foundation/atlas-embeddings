#!/usr/bin/env python3
"""
phase2_executor_evaluator.py — Phase 2 Executor & Evaluator Wrapper

Executes compiled Multiplicity programs and evaluates metrics.

This is a convenience wrapper around the Phase 2 executor module,
providing a simple CLI interface for the ship plan.

Usage:
    python phase2_executor_evaluator.py --program compiled.json --outdir results/ --seed 42

Outputs:
    - trace.jsonl: Per-operation execution trace
    - metrics.json: EVR, baseline, and relation metrics
"""

import argparse
import json
import os
import sys
from pathlib import Path

# Add sigmatics to path
REPO_ROOT = Path(__file__).parent.parent.parent
sys.path.insert(0, str(REPO_ROOT / "sigmatics" / "phase2"))

try:
    from executor import exec_program, run_executor_demo
except ImportError:
    print("Error: Phase 2 executor module not found", file=sys.stderr)
    print("Make sure sigmatics/phase2/executor.py exists", file=sys.stderr)
    sys.exit(1)


def main():
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Phase 2 — Executor & Evaluator",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Execute compiled program
  python phase2_executor_evaluator.py --program compiled.json --outdir results/

  # With custom seed
  python phase2_executor_evaluator.py --program compiled.json --outdir results/ --seed 123

  # Verbose output
  python phase2_executor_evaluator.py --program compiled.json --outdir results/ -v
        """
    )
    
    parser.add_argument(
        "--program",
        required=True,
        help="Compiled program JSON (from Phase 1)"
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
        print(f"Phase 2 Executor & Evaluator")
        print(f"Program: {args.program}")
        print(f"Output: {args.outdir}")
        print(f"Seed: {args.seed}")
        print()
    
    # Create output directory
    os.makedirs(args.outdir, exist_ok=True)
    
    # Execute program
    try:
        metrics = exec_program(program, outdir=args.outdir, seed=args.seed)
        
        if args.verbose:
            print(f"Execution complete")
            print(f"  EVR: {metrics.get('evr_A', 'N/A')}")
            print(f"  Baseline: {metrics.get('baseline_evr_A', {}).get('mean', 'N/A')}")
            print(f"  Wall time: {metrics.get('wall_time_exec_s', 'N/A')}s")
            print()
        
        # Write metrics
        metrics_path = os.path.join(args.outdir, "metrics.json")
        with open(metrics_path, "w") as f:
            json.dump(metrics, f, indent=2)
        
        print(f"Artifacts generated:")
        print(f"  - {os.path.join(args.outdir, 'trace.jsonl')}")
        print(f"  - {metrics_path}")
        
    except Exception as e:
        print(f"Error during execution: {e}", file=sys.stderr)
        if args.verbose:
            import traceback
            traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
