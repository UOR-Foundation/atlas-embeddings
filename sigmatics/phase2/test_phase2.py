#!/usr/bin/env python3
"""
Test Suite for Phase 2 Executor and Evaluator

This test suite validates:
1. Executor operations (rotate, permute, projector, etc.)
2. Signal path transformations
3. Relation path operations
4. Trace logging
5. Evaluator metrics computation
6. End-to-end execution
"""

import sys
import json
import tempfile
import os
from pathlib import Path

# Add phase2 to path
sys.path.insert(0, str(Path(__file__).parent))

import numpy as np
from executor import (
    Executor, ExecState, Policies, Trace,
    rotate_Rk, projector_A, projector_Delta,
    make_ring_graph, edges_of, quotient_graph_mod,
    permute_nodes, rotate_graph, jaccard_edges,
    energy_ratio, random_baseline_evr, retrieval_uplift,
    relation_consistency, run, admissible, N
)


def test_admissibility():
    """Test admissibility checks."""
    print("Test: Admissibility")
    
    # Valid for n = 12288 = 2^12 × 3^1
    assert admissible(2, 1, N), "2^1 should divide 12288"
    assert admissible(2, 12, N), "2^12 should divide 12288"
    assert admissible(3, 1, N), "3^1 should divide 12288"
    
    # Invalid
    assert not admissible(5, 1, N), "5 should not divide 12288"
    assert not admissible(2, 13, N), "2^13 should not divide 12288"
    assert not admissible(3, 2, N), "3^2 should not divide 12288"
    
    print("  ✓ Admissibility checks work correctly")


def test_rotate_Rk():
    """Test cyclic rotation."""
    print("Test: Rotation R^k")
    
    x = np.array([1.0, 2.0, 3.0, 4.0, 5.0])
    
    # Rotate by 0 (identity)
    y = rotate_Rk(x, 0)
    assert np.allclose(y, x), "Rotation by 0 should be identity"
    
    # Rotate by 1
    y = rotate_Rk(x, 1)
    expected = np.array([5.0, 1.0, 2.0, 3.0, 4.0])
    assert np.allclose(y, expected), f"Expected {expected}, got {y}"
    
    # Rotate by -1 (same as 4)
    y = rotate_Rk(x, -1)
    expected = np.array([2.0, 3.0, 4.0, 5.0, 1.0])
    assert np.allclose(y, expected), f"Expected {expected}, got {y}"
    
    # Rotate by size (identity)
    y = rotate_Rk(x, 5)
    assert np.allclose(y, x), "Rotation by size should be identity"
    
    print("  ✓ Rotation works correctly")


def test_projector_A():
    """Test A^{(m)} projector."""
    print("Test: Projector A^{(m)}")
    
    # Simple case: constant per residue class
    x = np.array([1.0, 2.0, 3.0, 4.0, 5.0, 6.0])
    y = projector_A(x, 2)
    
    # Indices 0,2,4 should have mean (1+3+5)/3 = 3
    # Indices 1,3,5 should have mean (2+4+6)/3 = 4
    expected = np.array([3.0, 4.0, 3.0, 4.0, 3.0, 4.0])
    assert np.allclose(y, expected), f"Expected {expected}, got {y}"
    
    # Projector is idempotent: A(A(x)) = A(x)
    y2 = projector_A(y, 2)
    assert np.allclose(y, y2), "A should be idempotent"
    
    print("  ✓ Projector A works correctly")


def test_projector_Delta():
    """Test Δ_{(m)} projector."""
    print("Test: Projector Δ_{(m)}")
    
    x = np.array([1.0, 2.0, 3.0, 4.0, 5.0, 6.0])
    Ax = projector_A(x, 2)
    Dx = projector_Delta(x, 2)
    
    # Δ = I - A, so x = A(x) + Δ(x)
    reconstructed = Ax + Dx
    assert np.allclose(x, reconstructed), "x should equal A(x) + Δ(x)"
    
    # Δ and A are orthogonal: <A(x), Δ(x)> = 0
    dot_product = np.dot(Ax, Dx)
    assert abs(dot_product) < 1e-10, f"A and Δ should be orthogonal, got {dot_product}"
    
    print("  ✓ Projector Δ works correctly")


def test_ring_graph():
    """Test ring graph construction."""
    print("Test: Ring graph")
    
    H = make_ring_graph(5)
    assert len(H) == 5, "Should have 5 nodes"
    
    # Check edges: 0→1, 1→2, 2→3, 3→4, 4→0
    assert H[0] == [1], f"Node 0 should point to 1, got {H[0]}"
    assert H[4] == [0], f"Node 4 should point to 0, got {H[4]}"
    
    # Check total edges
    E = edges_of(H)
    assert len(E) == 5, f"Should have 5 edges, got {len(E)}"
    
    print("  ✓ Ring graph construction works correctly")


def test_quotient_graph():
    """Test quotient graph modulo m."""
    print("Test: Quotient graph")
    
    # Ring of 6 nodes: 0→1→2→3→4→5→0
    H = make_ring_graph(6)
    
    # Quotient mod 2: 0→1→0
    Hq = quotient_graph_mod(H, 2)
    assert len(Hq) == 2, "Quotient should have 2 nodes"
    
    # Edges: 0→1, 1→0 (from 0→1, 1→2→0, 2→3, ...)
    Eq = set(edges_of(Hq))
    assert (0, 1) in Eq, "Should have edge 0→1"
    assert (1, 0) in Eq, "Should have edge 1→0"
    
    print("  ✓ Quotient graph works correctly")


def test_rotate_graph():
    """Test graph rotation."""
    print("Test: Graph rotation")
    
    H = make_ring_graph(4)
    # Original: 0→1→2→3→0
    
    # Rotate by 1: 1→2→3→0→1
    Hr = rotate_graph(H, 1)
    E = set(edges_of(Hr))
    
    # After rotation: node i becomes (i+1)%4
    # Original edge 0→1 becomes 1→2
    assert (1, 2) in E, "Should have edge 1→2"
    assert (0, 1) in E, "Should have edge 0→1"
    
    print("  ✓ Graph rotation works correctly")


def test_permute_nodes():
    """Test node permutation."""
    print("Test: Node permutation")
    
    H = make_ring_graph(3)
    # Original: 0→1→2→0
    
    # Swap nodes 0 and 1: π = [1, 0, 2]
    pi = [1, 0, 2]
    Hp = permute_nodes(H, pi)
    E = set(edges_of(Hp))
    
    # Original edge 0→1 becomes 1→0 (since 0 maps to 1)
    # Original edge 1→2 becomes 0→2 (since 1 maps to 0)
    assert (1, 0) in E, "Should have edge 1→0"
    assert (0, 2) in E, "Should have edge 0→2"
    
    print("  ✓ Node permutation works correctly")


def test_jaccard():
    """Test Jaccard similarity."""
    print("Test: Jaccard similarity")
    
    E1 = [(0, 1), (1, 2), (2, 3)]
    E2 = [(0, 1), (1, 2), (3, 4)]
    
    # Intersection: {(0,1), (1,2)} size 2
    # Union: {(0,1), (1,2), (2,3), (3,4)} size 4
    # Jaccard = 2/4 = 0.5
    j = jaccard_edges(E1, E2)
    assert abs(j - 0.5) < 1e-10, f"Expected 0.5, got {j}"
    
    # Identity
    j = jaccard_edges(E1, E1)
    assert abs(j - 1.0) < 1e-10, f"Expected 1.0, got {j}"
    
    print("  ✓ Jaccard similarity works correctly")


def test_executor_copy():
    """Test executor copy operation."""
    print("Test: Executor copy")
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.jsonl', delete=False) as f:
        trace_path = f.name
    
    try:
        trace = Trace(trace_path)
        executor = Executor(Policies(), trace)
        
        x0 = np.array([1.0, 2.0, 3.0])
        H0 = make_ring_graph(3)
        st = ExecState(x=x0.copy(), H={u: vs[:] for u, vs in H0.items()})
        
        w = {"op": "copy"}
        st = executor.step(w, st)
        
        # Copy should preserve x
        assert np.allclose(st.x, x0), "Copy should preserve signal"
        
        trace.close()
        
        # Check trace
        with open(trace_path, 'r') as f:
            lines = f.readlines()
            assert len(lines) == 1, "Should have 1 trace entry"
            rec = json.loads(lines[0])
            assert rec["op"] == "copy", "Operation should be copy"
            assert "pre" in rec and "post" in rec, "Should have pre/post stats"
    finally:
        os.unlink(trace_path)
    
    print("  ✓ Executor copy works correctly")


def test_executor_rotate():
    """Test executor rotate operation."""
    print("Test: Executor rotate")
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.jsonl', delete=False) as f:
        trace_path = f.name
    
    try:
        trace = Trace(trace_path)
        executor = Executor(Policies(), trace)
        
        x0 = np.array([1.0, 2.0, 3.0, 4.0])
        H0 = make_ring_graph(4)
        st = ExecState(x=x0.copy(), H={u: vs[:] for u, vs in H0.items()})
        
        w = {"op": "rotate", "k": 1}
        st = executor.step(w, st)
        
        # Check signal rotated
        expected = np.array([4.0, 1.0, 2.0, 3.0])
        assert np.allclose(st.x, expected), f"Expected {expected}, got {st.x}"
        
        trace.close()
    finally:
        os.unlink(trace_path)
    
    print("  ✓ Executor rotate works correctly")


def test_executor_projector():
    """Test executor projector operation."""
    print("Test: Executor projector")
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.jsonl', delete=False) as f:
        trace_path = f.name
    
    try:
        trace = Trace(trace_path)
        executor = Executor(Policies(), trace)
        
        x0 = np.array([1.0, 2.0, 3.0, 4.0, 5.0, 6.0])
        H0 = make_ring_graph(6)
        st = ExecState(x=x0.copy(), H={u: vs[:] for u, vs in H0.items()})
        
        # Apply A^{(2)}
        w = {"op": "projector", "p": 2, "r": 1, "mode": "A"}
        st = executor.step(w, st)
        
        # Check that A was applied
        expected = projector_A(x0, 2)
        assert np.allclose(st.x, expected), f"Expected projector A result"
        
        # Check that H was contracted
        assert len(st.H) == 2, f"H should have 2 nodes after quotient, got {len(st.H)}"
        
        trace.close()
    finally:
        os.unlink(trace_path)
    
    print("  ✓ Executor projector works correctly")


def test_energy_ratio():
    """Test energy ratio computation."""
    print("Test: Energy ratio")
    
    x = np.array([3.0, 4.0])
    y = np.array([1.0, 2.0])
    
    # E(x) = 9 + 16 = 25
    # E(y) = 1 + 4 = 5
    # ratio = 5/25 = 0.2
    ratio = energy_ratio(x, y)
    assert abs(ratio - 0.2) < 1e-10, f"Expected 0.2, got {ratio}"
    
    print("  ✓ Energy ratio works correctly")


def test_run_simple_program():
    """Test running a simple program end-to-end."""
    print("Test: Run simple program")
    
    program = {
        "n": N,
        "words": [
            {"op": "copy"},
            {"op": "rotate", "k": 10},
            {"op": "projector", "p": 3, "r": 1, "mode": "Δ"}
        ],
        "obligations": []
    }
    
    with tempfile.TemporaryDirectory() as tmpdir:
        metrics = run(program, tmpdir, seed=42)
        
        # Check outputs exist
        assert os.path.exists(os.path.join(tmpdir, "program.json")), "program.json should exist"
        assert os.path.exists(os.path.join(tmpdir, "trace.jsonl")), "trace.jsonl should exist"
        assert os.path.exists(os.path.join(tmpdir, "metrics.json")), "metrics.json should exist"
        
        # Check metrics structure
        assert "n" in metrics, "Should have n"
        assert "evr_A" in metrics, "Should have evr_A"
        assert "evr_Delta" in metrics, "Should have evr_Delta"
        assert "retrieval_uplift" in metrics, "Should have retrieval_uplift"
        assert "relation_consistency" in metrics, "Should have relation_consistency"
        
        # Check trace
        with open(os.path.join(tmpdir, "trace.jsonl"), 'r') as f:
            lines = f.readlines()
            assert len(lines) == 3, f"Should have 3 trace entries, got {len(lines)}"
            
            # Check first entry
            rec = json.loads(lines[0])
            assert rec["op"] == "copy", "First op should be copy"
    
    print("  ✓ End-to-end execution works correctly")


def run_all_tests():
    """Run all tests."""
    print("=" * 70)
    print("Phase 2 Test Suite")
    print("=" * 70)
    print()
    
    tests = [
        test_admissibility,
        test_rotate_Rk,
        test_projector_A,
        test_projector_Delta,
        test_ring_graph,
        test_quotient_graph,
        test_rotate_graph,
        test_permute_nodes,
        test_jaccard,
        test_executor_copy,
        test_executor_rotate,
        test_executor_projector,
        test_energy_ratio,
        test_run_simple_program,
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except Exception as e:
            print(f"  ✗ Test failed: {e}")
            failed += 1
        print()
    
    print("=" * 70)
    print(f"Results: {passed} passed, {failed} failed")
    print("=" * 70)
    
    return failed == 0


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
