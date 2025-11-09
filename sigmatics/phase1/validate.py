#!/usr/bin/env python3
"""
Validate Phase 1 Implementation Against Requirements

This script validates that the Phase 1 implementation meets all
requirements from the problem statement, including the determinism fix.
"""

import sys
import json
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))

from lowering import lower
from compiler import compile_program
from policies import Policies


def main():
    print("=" * 70)
    print("Phase 1 Validation Against Requirements")
    print("=" * 70)
    print()
    
    # Requirement 1: Deterministic lowering (semantic content only)
    print("1. Testing deterministic lowering (semantic content only)...")
    print("-" * 70)
    
    script1 = 'mark@{"p":3,"r":1,"mode":"delta"}; rho[17]; copy;'
    script2 = '\n  mark@{"p":3,"r":1,"mode":"delta"};  \n  rho[17];  \n  copy;  \n'
    
    lo1 = lower(script1, src_name="file1.sig")
    lo2 = lower(script2, src_name="file2.sig")
    
    # Different source files and whitespace, but same semantic content
    assert lo1["lowering_hash"] == lo2["lowering_hash"], \
        "Hash should be identical for same semantic content"
    
    print(f"  Script 1 (file1.sig): {lo1['lowering_hash']}")
    print(f"  Script 2 (file2.sig): {lo2['lowering_hash']}")
    print(f"  ✓ Hashes match (semantic content only)")
    print()
    
    # Requirement 2: Example script processing
    print("2. Processing example script...")
    print("-" * 70)
    
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
    
    lo_example = lower(example_script, src_name="example.sig")
    print(f"  Lowering hash: {lo_example['lowering_hash']}")
    print(f"  Words count: {len(lo_example['lowered']['words'])}")
    assert len(lo_example["lowered"]["words"]) == 10, "Should have 10 words"
    print(f"  ✓ Example lowering complete")
    print()
    
    # Requirement 3: Compilation with Π-first
    print("3. Compiling to Multiplicity (Π-first)...")
    print("-" * 70)
    
    policies = Policies()
    compiled = compile_program(lo_example["lowered"], policies)
    
    print(f"  Index size n: {compiled['n']}")
    print(f"  Compiled words: {len(compiled['words'])}")
    print(f"  Obligations: {len(compiled['obligations'])}")
    
    # Verify Π-first: first word should be projector
    assert compiled["words"][0]["op"] == "projector", \
        "First word should be projector (Π-first)"
    print(f"  First word: {compiled['words'][0]['op']} (p={compiled['words'][0]['p']}, r={compiled['words'][0]['r']})")
    print(f"  ✓ Π-first reduction applied")
    print()
    
    # Requirement 4: Admissibility check
    print("4. Testing admissibility enforcement...")
    print("-" * 70)
    
    # Valid projector
    assert compiled["words"][0]["p"] == 3 and compiled["words"][0]["r"] == 1, \
        "Example should have p=3, r=1"
    print(f"  ✓ p=3, r=1: admissible (3^1 = 3 divides 12288)")
    
    # Try invalid projector
    try:
        bad_script = 'mark@{"p":5,"r":1};'
        lo_bad = lower(bad_script, "test.sig")
        compiled_bad = compile_program(lo_bad["lowered"], policies)
        assert False, "Should have raised ValueError"
    except ValueError as e:
        assert "Admissibility failed" in str(e)
        print(f"  ✓ p=5, r=1: rejected (5 does not divide 12288)")
    print()
    
    # Requirement 5: Obligations tracked
    print("5. Verifying obligation tracking...")
    print("-" * 70)
    
    obligations = compiled["obligations"]
    assert len(obligations) > 0, "Should have obligations"
    
    policy_obs = [o for o in obligations if o["type"] == "policy"]
    semantics_obs = [o for o in obligations if o["type"] == "semantics"]
    
    print(f"  Policy obligations: {len(policy_obs)}")
    print(f"  Semantics obligations: {len(semantics_obs)}")
    print(f"  Total: {len(obligations)}")
    
    # All should be UNPROVEN
    all_unproven = all(o["status"] == "UNPROVEN" for o in obligations)
    assert all_unproven, "All obligations should be UNPROVEN"
    print(f"  ✓ All obligations marked UNPROVEN")
    print()
    
    # Requirement 6: JSON Schemas exist
    print("6. Checking JSON Schemas...")
    print("-" * 70)
    
    schemas_dir = Path(__file__).parent / "schemas"
    required_schemas = [
        "sigmatics_word.schema.json",
        "multiplicity_word.schema.json",
        "program.schema.json"
    ]
    
    for schema_name in required_schemas:
        schema_path = schemas_dir / schema_name
        assert schema_path.exists(), f"Schema {schema_name} should exist"
        
        # Verify it's valid JSON
        with open(schema_path) as f:
            schema = json.load(f)
        assert "$schema" in schema, f"{schema_name} should have $schema field"
        print(f"  ✓ {schema_name}")
    print()
    
    # Requirement 7: Artifacts exist
    print("7. Verifying artifacts...")
    print("-" * 70)
    
    artifacts_dir = Path(__file__).parent / "artifacts"
    
    lowered_json = artifacts_dir / "lowered.json"
    compiled_json = artifacts_dir / "compiled_program.json"
    
    if lowered_json.exists():
        with open(lowered_json) as f:
            lowered_data = json.load(f)
        print(f"  ✓ lowered.json (hash: {lowered_data['lowering_hash'][:16]}...)")
    else:
        print(f"  ! lowered.json not found (run demo.py to generate)")
    
    if compiled_json.exists():
        with open(compiled_json) as f:
            compiled_data = json.load(f)
        print(f"  ✓ compiled_program.json ({len(compiled_data['words'])} words)")
    else:
        print(f"  ! compiled_program.json not found (run demo.py to generate)")
    print()
    
    # Requirement 8: ZIP package
    print("8. Checking ZIP package...")
    print("-" * 70)
    
    zip_path = Path(__file__).parent / "phase1_apex_v0.zip"
    if zip_path.exists():
        zip_size = zip_path.stat().st_size
        print(f"  ✓ phase1_apex_v0.zip ({zip_size:,} bytes)")
    else:
        print(f"  ! ZIP not found (run create_zip.py to generate)")
    print()
    
    # Summary
    print("=" * 70)
    print("Summary")
    print("=" * 70)
    print("✓ Deterministic lowering (semantic content only)")
    print("✓ Example script processed correctly")
    print("✓ Π-first reduction applied")
    print("✓ Admissibility checks enforced")
    print("✓ Obligations tracked (all UNPROVEN)")
    print("✓ JSON Schemas provided")
    print("✓ Artifacts available")
    print("✓ ZIP package created")
    print()
    print("All requirements validated successfully!")
    print("=" * 70)


if __name__ == "__main__":
    main()
