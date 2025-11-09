#!/usr/bin/env python3
"""
Test Suite for Phase 3 Validation & KPIs

This test suite validates:
1. Unit property checks (idempotence, non-commutation, rotation closure)
2. Round-trip integrity
3. KPI computation
4. Integration with Phase 1 and Phase 2
"""

import sys
import json
import tempfile
import os
from pathlib import Path

# Add phase3 to path
sys.path.insert(0, str(Path(__file__).parent))

import numpy as np
from phase3 import (
    N, PAGE_SIZE, PAGES,
    tokenize, parse_stmt, lower, Policies, admissible,
    compile_words, compile_program, pretty_print_program,
    rotate_Rk, projector_A, projector_Delta,
    make_ring_graph, edges_of, quotient_graph_mod,
    exec_program, unit_projector_idempotence,
    witness_perm_q, unit_noncommutation_witness,
    unit_rotation_closure, unit_split_merge_roundtrip,
    roundtrip_check, determinism_rate, obligation_counts
)


def test_constants():
    """Test that constants are correctly defined."""
    print("Test: Constants")
    assert N == 12288, f"N should be 12288, got {N}"
    assert PAGE_SIZE == 256, f"PAGE_SIZE should be 256, got {PAGE_SIZE}"
    assert PAGES == 48, f"PAGES should be 48, got {PAGES}"
    print("  ✓ Constants are correct")


def test_projector_idempotence():
    """Test that projectors are idempotent: A² = A and Δ² = Δ."""
    print("Test: Projector idempotence")
    
    result = unit_projector_idempotence(trials=3, seeds=[10, 11, 12])
    
    # Check structure
    assert "A" in result, "Result should contain 'A'"
    assert "Delta" in result, "Result should contain 'Delta'"
    assert len(result["A"]) == 3, f"Should have 3 A results, got {len(result['A'])}"
    assert len(result["Delta"]) == 3, f"Should have 3 Delta results, got {len(result['Delta'])}"
    
    # Check idempotence (errors should be very small)
    for item in result["A"]:
        assert item["max_abs_err"] < 1e-10, f"A idempotence error too large: {item['max_abs_err']}"
    
    for item in result["Delta"]:
        assert item["max_abs_err"] < 1e-10, f"Δ idempotence error too large: {item['max_abs_err']}"
    
    print("  ✓ Projectors are idempotent")


def test_witness_permutation():
    """Test witness permutation construction."""
    print("Test: Witness permutation W^(q)")
    
    # q=5 is coprime to 256
    pi = witness_perm_q(5)
    
    assert len(pi) == N, f"Permutation should have length {N}, got {len(pi)}"
    assert len(set(pi)) == N, "Permutation should have all unique elements"
    assert set(pi) == set(range(N)), "Permutation should be a bijection"
    
    # Check page boundaries are preserved
    for page in range(PAGES):
        base = page * PAGE_SIZE
        page_elements = pi[base:base+PAGE_SIZE]
        page_bases = [p // PAGE_SIZE for p in page_elements]
        assert all(b == page for b in page_bases), f"Page {page} boundaries violated"
    
    print("  ✓ Witness permutation constructed correctly")


def test_noncommutation_witness():
    """Test non-commutation witness: A_p W_q ≠ W_q A_p."""
    print("Test: Non-commutation witness")
    
    result = unit_noncommutation_witness(p=3, q=5, trials=5)
    
    assert result["p"] == 3, "p should be 3"
    assert result["q"] == 5, "q should be 5"
    assert result["trials"] == 5, "Should have 5 trials"
    
    # Should find non-commutation in all or most trials
    assert result["noncommute_trials"] >= 4, f"Should find non-commutation in most trials, got {result['noncommute_trials']}/5"
    assert result["max_diff"] > 1e-6, "Max difference should be significant"
    
    print(f"  ✓ Non-commutation detected in {result['noncommute_trials']}/{result['trials']} trials")


def test_rotation_closure():
    """Test rotation closure: R^n = Identity."""
    print("Test: Rotation closure")
    
    result = unit_rotation_closure()
    
    assert "R^n_identity_max_abs_err" in result, "Result should contain error metric"
    assert result["R^n_identity_max_abs_err"] < 1e-10, f"Rotation closure error too large: {result['R^n_identity_max_abs_err']}"
    
    print("  ✓ Rotation closure verified")


def test_split_merge_roundtrip():
    """Test split-merge round-trip consistency."""
    print("Test: Split-merge round-trip")
    
    result = unit_split_merge_roundtrip(m=3)
    
    assert "contracted_edges" in result, "Result should contain contracted_edges"
    assert "roundtrip_equal" in result, "Result should contain roundtrip_equal"
    assert result["contracted_edges"] == 3, f"Should have 3 contracted edges, got {result['contracted_edges']}"
    assert result["roundtrip_equal"], "Round-trip should preserve structure"
    
    print("  ✓ Split-merge round-trip consistent")


def test_roundtrip_check():
    """Test round-trip integrity: source → lowered → compiled → pretty → lowered'."""
    print("Test: Round-trip check")
    
    script = """
        mark@{"p":3,"r":1,"mode":"delta"};
        rho[7];
        copy;
    """
    
    result = roundtrip_check(script)
    
    assert "lowering_hash_1" in result, "Result should contain first hash"
    assert "lowering_hash_2" in result, "Result should contain second hash"
    assert "hash_equal" in result, "Result should contain hash_equal"
    assert "structure_equal" in result, "Result should contain structure_equal"
    assert "pretty_script" in result, "Result should contain pretty_script"
    
    # For supported subset, hashes should match
    assert result["hash_equal"], "Round-trip hashes should match for supported subset"
    
    print("  ✓ Round-trip integrity verified")


def test_determinism_rate():
    """Test determinism rate of lowering."""
    print("Test: Determinism rate")
    
    script = "mark@{\"p\":3}; copy;"
    rate = determinism_rate(script, variants=10)
    
    assert 0.0 <= rate <= 1.0, f"Rate should be between 0 and 1, got {rate}"
    assert rate == 1.0, f"Lowering should be fully deterministic, got {rate}"
    
    print(f"  ✓ Determinism rate: {rate:.1%}")


def test_obligation_counts():
    """Test obligation counting."""
    print("Test: Obligation counts")
    
    script = 'mark@{"p":3,"r":1}; quote; evaluate;'
    lowered = lower(script, src_name="test.sig")
    program = compile_program(lowered["lowered"], Policies())
    
    counts = obligation_counts(program)
    
    assert "UNPROVEN" in counts, "Counts should contain UNPROVEN"
    assert "VIOLATION" in counts, "Counts should contain VIOLATION"
    assert counts["UNPROVEN"] > 0, "Should have some UNPROVEN obligations"
    assert counts["VIOLATION"] == 0, "Should have no violations for valid program"
    
    print(f"  ✓ Obligation counts: {counts['UNPROVEN']} UNPROVEN, {counts['VIOLATION']} VIOLATION")


def test_exec_program():
    """Test program execution."""
    print("Test: Program execution")
    
    script = 'mark@{"p":3,"r":1,"mode":"delta"}; rho[7]; copy;'
    lowered = lower(script, src_name="test.sig")
    program = compile_program(lowered["lowered"], Policies())
    
    with tempfile.TemporaryDirectory() as tmpdir:
        metrics = exec_program(program, tmpdir, seed=42)
        
        # Check metrics structure
        assert "n" in metrics, "Metrics should contain n"
        assert "evr_A" in metrics, "Metrics should contain evr_A"
        assert "evr_Delta" in metrics, "Metrics should contain evr_Delta"
        assert "baseline_evr_A" in metrics, "Metrics should contain baseline_evr_A"
        assert metrics["n"] == N, f"n should be {N}, got {metrics['n']}"
        
        # Check files created
        assert os.path.exists(os.path.join(tmpdir, "program.json")), "program.json should be created"
        assert os.path.exists(os.path.join(tmpdir, "trace.jsonl")), "trace.jsonl should be created"
        assert os.path.exists(os.path.join(tmpdir, "metrics.json")), "metrics.json should be created"
    
    print("  ✓ Program execution completed successfully")


def test_end_to_end():
    """Test complete end-to-end pipeline."""
    print("Test: End-to-end pipeline")
    
    script = """
        mark@{"p":3,"r":1,"mode":"delta"};
        rho[17];
        copy;
        split@ℓ:int;
        merge;
    """
    
    # Phase 1: Lower and compile
    lowered = lower(script, src_name="test.sig")
    program = compile_program(lowered["lowered"], Policies())
    
    assert "n" in program, "Program should contain n"
    assert "words" in program, "Program should contain words"
    assert "obligations" in program, "Program should contain obligations"
    assert program["n"] == N, f"n should be {N}"
    assert len(program["words"]) > 0, "Should have compiled words"
    
    # Phase 2: Execute
    with tempfile.TemporaryDirectory() as tmpdir:
        metrics = exec_program(program, tmpdir, seed=42)
        
        assert metrics["n"] == N, f"Metrics n should be {N}"
        
        # Phase 3 validations
        idempotence = unit_projector_idempotence(trials=2)
        assert len(idempotence["A"]) == 2, "Should have 2 idempotence tests"
        
        noncommute = unit_noncommutation_witness(p=3, q=5, trials=3)
        assert noncommute["trials"] == 3, "Should have 3 non-commutation trials"
        
        rt = roundtrip_check(script)
        assert rt["hash_equal"], "Round-trip hashes should match"
        
        det = determinism_rate(script, variants=5)
        assert det == 1.0, "Should be fully deterministic"
        
        oblig = obligation_counts(program)
        assert oblig["UNPROVEN"] > 0, "Should have UNPROVEN obligations"
    
    print("  ✓ End-to-end pipeline completed successfully")


def run_all_tests():
    """Run all tests."""
    print("=" * 70)
    print("Phase 3 Test Suite")
    print("=" * 70)
    print()
    
    tests = [
        test_constants,
        test_projector_idempotence,
        test_witness_permutation,
        test_noncommutation_witness,
        test_rotation_closure,
        test_split_merge_roundtrip,
        test_roundtrip_check,
        test_determinism_rate,
        test_obligation_counts,
        test_exec_program,
        test_end_to_end,
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
            print()
        except Exception as e:
            failed += 1
            print(f"  ✗ FAILED: {e}")
            print()
    
    print("=" * 70)
    print(f"Results: {passed} passed, {failed} failed")
    print("=" * 70)
    
    return failed == 0


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
