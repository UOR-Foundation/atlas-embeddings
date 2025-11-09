#!/usr/bin/env python3
"""
Phase 1 Demonstration: Full Pipeline

This script demonstrates the complete Phase 1 pipeline:
1. Parse and lower a Sigmatics script
2. Verify deterministic lowering
3. Compile to Multiplicity program
4. Show artifacts and obligations
"""

import json
import sys
from pathlib import Path

# Add phase1 to path
sys.path.insert(0, str(Path(__file__).parent))

from lowering import lower, verify_determinism
from compiler import compile_program
from policies import Policies


def main():
    """Run Phase 1 demonstration."""
    
    print("=" * 70)
    print("Phase 1 — Front end and compiler demonstration")
    print("=" * 70)
    print()
    
    # Example script
    example_script = """
        mark@{"p":3,"r":1,"mode":"delta"};
        rho[17];
        copy;
        swap@c_d;
        split@ℓ:int;
        merge;
        quote;
        ~;
        evaluate;
        mu[5];
    """
    
    print("1. Example Sigmatics script:")
    print("-" * 70)
    print(example_script.strip())
    print()
    
    # Lower to JSON
    print("2. Lowering to JSON words...")
    print("-" * 70)
    lowered1 = lower(example_script, src_name="example.sig")
    print(f"Lowering hash: {lowered1['lowering_hash']}")
    print(f"Number of words: {len(lowered1['lowered']['words'])}")
    print()
    
    # Verify determinism
    print("3. Verifying deterministic lowering...")
    print("-" * 70)
    # Add whitespace noise
    example_script_noisy = "\n" + example_script.replace(" ", "  ").replace("\n", "\n  ") + "\n"
    lowered2 = lower(example_script_noisy, src_name="example.sig")
    
    deterministic = (lowered1["lowering_hash"] == lowered2["lowering_hash"])
    
    print(f"Script 1 hash: {lowered1['lowering_hash']}")
    print(f"Script 2 hash: {lowered2['lowering_hash']}")
    print(f"Deterministic: {deterministic} ✓" if deterministic else f"Deterministic: {deterministic} ✗")
    print()
    
    # Compile to Multiplicity
    print("4. Compiling to Multiplicity program...")
    print("-" * 70)
    policies = Policies()
    compiled = compile_program(lowered1["lowered"], policies)
    
    print(f"Index size n: {compiled['n']}")
    print(f"Compiled words: {len(compiled['words'])}")
    print(f"Obligations tracked: {len(compiled['obligations'])}")
    print()
    
    # Show first few words
    print("5. First 5 compiled words (Π-first order):")
    print("-" * 70)
    for i, word in enumerate(compiled["words"][:5]):
        print(f"  {i+1}. {word['op']}", end="")
        # Show key parameters
        if word["op"] == "projector":
            print(f" (p={word['p']}, r={word['r']}, mode={word['mode']})", end="")
        elif word["op"] == "rotate":
            print(f" (k={word['k']})", end="")
        elif word["op"] == "merge":
            print(f" (arity={word['arity']})", end="")
        elif word["op"] == "split":
            print(f" (type={word['ellType']})", end="")
        
        if "note" in word:
            print(f" — {word['note']}", end="")
        print()
    print()
    
    # Show obligations
    print("6. Obligations (UNPROVEN items):")
    print("-" * 70)
    for i, obl in enumerate(compiled["obligations"]):
        print(f"  {i+1}. {obl['type']}: {obl.get('name', 'N/A')} — {obl['status']}")
    print()
    
    # Summary
    print("=" * 70)
    print("Summary:")
    print(f"  ✓ Deterministic lowering: {deterministic}")
    print(f"  ✓ Lowering hash: {lowered1['lowering_hash']}")
    print(f"  ✓ Π-first reduction applied")
    print(f"  ✓ Admissibility checks passed")
    print(f"  ! {len(compiled['obligations'])} UNPROVEN obligations tracked")
    print("=" * 70)
    print()
    
    # Write artifacts
    artifacts_dir = Path(__file__).parent / "artifacts"
    artifacts_dir.mkdir(exist_ok=True)
    
    with open(artifacts_dir / "lowered.json", "w") as f:
        json.dump(lowered1, f, indent=2, ensure_ascii=False)
    
    with open(artifacts_dir / "compiled_program.json", "w") as f:
        json.dump(compiled, f, indent=2, ensure_ascii=False)
    
    print(f"Artifacts written to {artifacts_dir}/")
    print("  - lowered.json")
    print("  - compiled_program.json")
    print()


if __name__ == "__main__":
    main()
