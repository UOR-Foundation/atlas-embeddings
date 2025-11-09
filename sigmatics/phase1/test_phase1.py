#!/usr/bin/env python3
"""
Test Suite for Phase 1 Sigmatics Compiler

This test suite validates:
1. Lexer and parser functionality
2. Deterministic lowering
3. Admissibility checks
4. Π-first reduction
5. Obligation tracking
6. End-to-end compilation
"""

import sys
from pathlib import Path

# Add phase1 to path
sys.path.insert(0, str(Path(__file__).parent))

from lexer_parser import tokenize, parse_stmt, parse
from lowering import lower, verify_determinism
from policies import Policies, admissible, N
from compiler import compile_words, compile_program


def test_tokenize():
    """Test tokenization of Sigmatics script."""
    print("Test: Tokenization")
    script = "copy; mark@{\"p\":3}; ~;"
    tokens = tokenize(script)
    assert len(tokens) == 3, f"Expected 3 tokens, got {len(tokens)}"
    assert tokens[0][0] == "copy", f"First token should be 'copy', got {tokens[0][0]}"
    print("  ✓ Tokenization works correctly")


def test_parse_simple_ops():
    """Test parsing of simple operations."""
    print("Test: Simple operations parsing")
    
    assert parse_stmt("copy") == {"op": "copy", "args": {}}
    assert parse_stmt("~") == {"op": "mirror", "args": {}}
    assert parse_stmt("merge") == {"op": "merge", "args": {}}
    assert parse_stmt("quote") == {"op": "quote", "args": {}}
    assert parse_stmt("evaluate") == {"op": "evaluate", "args": {}}
    
    print("  ✓ Simple operations parse correctly")


def test_parse_complex_ops():
    """Test parsing of complex operations with arguments."""
    print("Test: Complex operations parsing")
    
    # swap
    result = parse_stmt("swap@c_d")
    assert result["op"] == "swap"
    assert result["args"]["c"] == "c"
    assert result["args"]["d"] == "d"
    
    # split
    result = parse_stmt("split@ℓ:int")
    assert result["op"] == "split"
    assert result["args"]["ellType"] == "int"
    
    # mark with JSON
    result = parse_stmt('mark@{"p":3,"r":1}')
    assert result["op"] == "mark"
    assert result["args"]["d"]["p"] == 3
    assert result["args"]["d"]["r"] == 1
    
    # rho
    result = parse_stmt("rho[17]")
    assert result["op"] == "control"
    assert result["args"]["kind"] == "rho"
    assert result["args"]["k"] == 17
    
    # tau
    result = parse_stmt("tau[-5]")
    assert result["op"] == "control"
    assert result["args"]["kind"] == "tau"
    assert result["args"]["k"] == -5
    
    # mu
    result = parse_stmt("mu[3]")
    assert result["op"] == "control"
    assert result["args"]["kind"] == "mu"
    assert result["args"]["p"] == 3
    
    print("  ✓ Complex operations parse correctly")


def test_deterministic_lowering():
    """Test that lowering is deterministic under whitespace changes."""
    print("Test: Deterministic lowering")
    
    script1 = "mark@{\"p\":3}; copy; ~;"
    script2 = "\n  mark@{\"p\":3};  \n copy;  ~;  \n"
    
    lo1 = lower(script1, "test")
    lo2 = lower(script2, "test")
    
    # Hashes should be identical
    assert lo1["lowering_hash"] == lo2["lowering_hash"], \
        f"Hashes differ: {lo1['lowering_hash']} vs {lo2['lowering_hash']}"
    
    # Verify using helper function
    assert verify_determinism(script1, script2, "test"), \
        "verify_determinism should return True"
    
    print(f"  ✓ Deterministic lowering (hash: {lo1['lowering_hash'][:16]}...)")


def test_admissibility():
    """Test admissibility checks."""
    print("Test: Admissibility checks")
    
    # n = 12288 = 2^12 × 3^1
    
    # Should be admissible
    assert admissible(2, 1, N), "2^1 should divide 12288"
    assert admissible(2, 8, N), "2^8 should divide 12288"
    assert admissible(2, 12, N), "2^12 should divide 12288"
    assert admissible(3, 1, N), "3^1 should divide 12288"
    
    # Should NOT be admissible
    assert not admissible(2, 13, N), "2^13 should not divide 12288"
    assert not admissible(3, 2, N), "3^2 should not divide 12288"
    assert not admissible(5, 1, N), "5 should not divide 12288"
    assert not admissible(7, 1, N), "7 should not divide 12288"
    
    print("  ✓ Admissibility checks work correctly")


def test_pi_first_reduction():
    """Test that Π-first reduction places projectors first."""
    print("Test: Π-first reduction")
    
    script = """
        copy;
        mark@{"p":3,"r":1};
        rho[5];
        mark@{"p":2,"r":2};
        merge;
    """
    
    lowered = lower(script, "test")
    policies = Policies()
    program = compile_program(lowered["lowered"], policies)
    
    # Count projectors at the start
    projector_count = 0
    for word in program["words"]:
        if word["op"] == "projector":
            projector_count += 1
        else:
            break  # Stop at first non-projector
    
    # Should have 2 projectors at the start
    assert projector_count == 2, \
        f"Expected 2 projectors at start, got {projector_count}"
    
    # Check that all projectors are indeed at the start
    all_projectors = [w for w in program["words"] if w["op"] == "projector"]
    assert len(all_projectors) == 2, \
        f"Expected 2 total projectors, got {len(all_projectors)}"
    
    print("  ✓ Π-first reduction places projectors first")


def test_obligation_tracking():
    """Test that UNPROVEN obligations are tracked."""
    print("Test: Obligation tracking")
    
    script = """
        mark@{"p":3,"r":1};
        swap@a_b;
        merge;
        quote;
    """
    
    lowered = lower(script, "test")
    policies = Policies()
    program = compile_program(lowered["lowered"], policies)
    
    obligations = program["obligations"]
    
    # Should have multiple obligations
    assert len(obligations) > 0, "Should have at least one obligation"
    
    # Check for specific obligation types
    has_policy = any(o["type"] == "policy" for o in obligations)
    has_semantics = any(o["type"] == "semantics" for o in obligations)
    
    assert has_policy, "Should have at least one policy obligation"
    assert has_semantics, "Should have at least one semantics obligation"
    
    # All should be UNPROVEN
    all_unproven = all(o["status"] == "UNPROVEN" for o in obligations)
    assert all_unproven, "All obligations should be UNPROVEN"
    
    print(f"  ✓ Obligation tracking ({len(obligations)} obligations tracked)")


def test_admissibility_violation():
    """Test that inadmissible projectors are rejected."""
    print("Test: Admissibility violation")
    
    # Try to compile with p=5, r=1 (inadmissible)
    script = 'mark@{"p":5,"r":1};'
    lowered = lower(script, "test")
    policies = Policies()
    
    try:
        program = compile_program(lowered["lowered"], policies)
        assert False, "Should have raised ValueError for inadmissible projector"
    except ValueError as e:
        assert "Admissibility failed" in str(e), \
            f"Error message should mention admissibility: {e}"
    
    print("  ✓ Inadmissible projectors are rejected")


def test_end_to_end():
    """Test end-to-end compilation pipeline."""
    print("Test: End-to-end compilation")
    
    script = """
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
    
    # Lower
    lowered = lower(script, "example.sig")
    assert "lowered" in lowered
    assert "lowering_hash" in lowered
    assert len(lowered["lowered"]["words"]) == 10
    
    # Compile
    policies = Policies()
    program = compile_program(lowered["lowered"], policies)
    
    assert program["n"] == 12288
    assert len(program["words"]) == 10
    assert len(program["obligations"]) > 0
    
    # Check Π-first
    first_word = program["words"][0]
    assert first_word["op"] == "projector", \
        f"First word should be projector, got {first_word['op']}"
    
    print("  ✓ End-to-end compilation works")


def run_all_tests():
    """Run all tests."""
    print("=" * 70)
    print("Phase 1 Sigmatics Compiler Test Suite")
    print("=" * 70)
    print()
    
    tests = [
        test_tokenize,
        test_parse_simple_ops,
        test_parse_complex_ops,
        test_deterministic_lowering,
        test_admissibility,
        test_pi_first_reduction,
        test_obligation_tracking,
        test_admissibility_violation,
        test_end_to_end,
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
            print()
        except AssertionError as e:
            print(f"  ✗ FAILED: {e}")
            print()
            failed += 1
        except Exception as e:
            print(f"  ✗ ERROR: {e}")
            print()
            failed += 1
    
    print("=" * 70)
    print(f"Results: {passed} passed, {failed} failed")
    print("=" * 70)
    
    return failed == 0


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
