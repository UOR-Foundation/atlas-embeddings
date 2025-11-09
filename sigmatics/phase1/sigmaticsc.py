#!/usr/bin/env python3
"""
Sigmatics Compiler CLI

Command-line tool for compiling Sigmatics scripts to Multiplicity programs.

Usage:
    python sigmaticsc.py <sigfile> [-o output.json]

Example:
    python sigmaticsc.py example.sig -o compiled_program.json
"""

import sys
import json
import argparse
from pathlib import Path

# Add phase1 to path
sys.path.insert(0, str(Path(__file__).parent))

from lowering import lower
from compiler import compile_program
from policies import Policies


def main():
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Compile Sigmatics scripts to Multiplicity programs"
    )
    parser.add_argument(
        "sigfile",
        help="Sigmatics script file (.sig)"
    )
    parser.add_argument(
        "-o", "--out",
        default="compiled_program.json",
        help="Output file (default: compiled_program.json)"
    )
    parser.add_argument(
        "--lowered",
        help="Also output lowered JSON (optional)"
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Verbose output"
    )
    
    args = parser.parse_args()
    
    # Read script
    try:
        with open(args.sigfile, "r", encoding="utf-8") as f:
            script = f.read()
    except FileNotFoundError:
        print(f"Error: File not found: {args.sigfile}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error reading file: {e}", file=sys.stderr)
        sys.exit(1)
    
    if args.verbose:
        print(f"Compiling {args.sigfile}...")
    
    # Lower to JSON
    try:
        lowered = lower(script, src_name=args.sigfile)
        if args.verbose:
            print(f"Lowering hash: {lowered['lowering_hash']}")
            print(f"Words count: {len(lowered['lowered']['words'])}")
    except Exception as e:
        print(f"Error during lowering: {e}", file=sys.stderr)
        sys.exit(1)
    
    # Compile to Multiplicity
    try:
        policies = Policies()
        program = compile_program(lowered["lowered"], policies)
        
        if args.verbose:
            print(f"Compiled words: {len(program['words'])}")
            print(f"Obligations: {len(program['obligations'])}")
    except ValueError as e:
        print(f"Compilation error: {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Unexpected error during compilation: {e}", file=sys.stderr)
        sys.exit(1)
    
    # Write output
    try:
        with open(args.out, "w", encoding="utf-8") as f:
            json.dump(program, f, indent=2, ensure_ascii=False)
        
        if args.verbose:
            print(f"Output written to {args.out}")
        else:
            print(args.out)
        
        # Optionally write lowered JSON
        if args.lowered:
            with open(args.lowered, "w", encoding="utf-8") as f:
                json.dump(lowered, f, indent=2, ensure_ascii=False)
            if args.verbose:
                print(f"Lowered JSON written to {args.lowered}")
                
    except Exception as e:
        print(f"Error writing output: {e}", file=sys.stderr)
        sys.exit(1)
    
    # Report warnings for UNPROVEN obligations
    if args.verbose and program["obligations"]:
        print("\nWarnings:")
        unproven = [o for o in program["obligations"] if o.get("status") == "UNPROVEN"]
        if unproven:
            print(f"  {len(unproven)} UNPROVEN obligations (policies/semantics need verification)")


if __name__ == "__main__":
    main()
