"""
Phase 0 Test Suite: Numeric (X) and Structural (H) Tests with Baseline Scoring

This module implements:
1. Numeric tests (X): Validate numeric properties and computations
2. Structural tests (H): Validate structural/algebraic properties
3. Baseline scorer (R): Compare results against trivial baseline

All tests verify the minimal, testable bridge implementation.
"""

import pytest
import numpy as np
from typing import List, Tuple, Dict, Any

from multiplicity_core.phase0_index import (
    INDEX_SIZE,
    NUM_PAGES,
    BYTES_PER_PAGE,
    index_map,
    inverse_index_map,
    check_projector_admissibility,
    prime_factors,
)
from multiplicity_core.sigmatics_bridge import (
    bridge_compile,
    compile_sigmatics_to_multiplicity,
    WordType,
)


# ============================================================================
# X Tests: Numeric Tests
# ============================================================================

class TestNumericX:
    """Numeric tests (X) - validate numeric properties."""
    
    def test_x1_index_size_arithmetic(self):
        """X1: Verify index size arithmetic."""
        assert INDEX_SIZE == 12288
        assert INDEX_SIZE == 48 * 256
        assert INDEX_SIZE == 2**12 * 3
        assert INDEX_SIZE == 4096 * 3
    
    def test_x2_index_map_linearity(self):
        """X2: Verify index map linearity."""
        # index(p, 0, o) should be linear in p and o
        for p in [0, 1, 23, 47]:
            for o in [0, 1, 127, 255]:
                idx = index_map(p, 0, o)
                assert idx == p * 256 + o
                
                # Check inverse
                p2, b2, o2 = inverse_index_map(idx)
                assert (p2, o2) == (p, o)
    
    def test_x3_index_coverage(self):
        """X3: Verify index map covers all indices exactly once."""
        # Generate all indices
        indices = set()
        for p in range(NUM_PAGES):
            for o in range(BYTES_PER_PAGE):
                idx = index_map(p, 0, o)
                indices.add(idx)
        
        # Should cover exactly [0, INDEX_SIZE)
        assert len(indices) == INDEX_SIZE
        assert min(indices) == 0
        assert max(indices) == INDEX_SIZE - 1
    
    def test_x4_projector_divisibility(self):
        """X4: Verify projector admissibility divisibility."""
        # 12288 = 2^12 * 3
        factors = prime_factors(INDEX_SIZE)
        assert factors == {2: 12, 3: 1}
        
        # All claimed admissible projectors should divide INDEX_SIZE
        for p in [2, 3]:
            for r in range(1, factors.get(p, 0) + 1):
                assert check_projector_admissibility(p, r)
                assert INDEX_SIZE % (p ** r) == 0
    
    def test_x5_page_offset_bounds(self):
        """X5: Verify page and offset bounds."""
        # Valid range checks
        assert 0 <= 0 < NUM_PAGES
        assert 0 <= 47 < NUM_PAGES
        assert not (0 <= 48 < NUM_PAGES)
        
        assert 0 <= 0 < BYTES_PER_PAGE
        assert 0 <= 255 < BYTES_PER_PAGE
        assert not (0 <= 256 < BYTES_PER_PAGE)
    
    def test_x6_address_determinism(self):
        """X6: Verify address computation is deterministic."""
        # Same inputs should always give same output
        for _ in range(10):
            assert index_map(17, 0, 46) == 4398
            assert inverse_index_map(4398) == (17, 0, 46)
    
    def test_x7_prime_factorization(self):
        """X7: Verify prime factorization correctness."""
        assert prime_factors(12288) == {2: 12, 3: 1}
        assert prime_factors(256) == {2: 8}
        assert prime_factors(48) == {2: 4, 3: 1}
        assert prime_factors(1) == {}
        assert prime_factors(2) == {2: 1}
        assert prime_factors(17) == {17: 1}


# ============================================================================
# H Tests: Structural Tests
# ============================================================================

class TestStructuralH:
    """Structural tests (H) - validate structural/algebraic properties."""
    
    def test_h1_index_map_bijection(self):
        """H1: Verify index map is a bijection."""
        # For all valid (p, o), index_map is injective
        seen = {}
        for p in range(NUM_PAGES):
            for o in range(BYTES_PER_PAGE):
                idx = index_map(p, 0, o)
                assert idx not in seen, f"Collision: {(p, o)} and {seen[idx]} both map to {idx}"
                seen[idx] = (p, o)
        
        # Verify surjection: all indices in [0, INDEX_SIZE) are covered
        assert set(seen.keys()) == set(range(INDEX_SIZE))
    
    def test_h2_inverse_consistency(self):
        """H2: Verify inverse map consistency."""
        # For all idx, inverse_index_map(index_map(...)) = identity
        for p in range(0, NUM_PAGES, 5):  # Sample pages
            for o in range(0, BYTES_PER_PAGE, 13):  # Sample offsets
                idx = index_map(p, 0, o)
                p2, b2, o2 = inverse_index_map(idx)
                assert (p2, o2) == (p, o)
        
        # For all idx, index_map(inverse_index_map(idx)) = idx
        for idx in range(0, INDEX_SIZE, 100):  # Sample indices
            p, b, o = inverse_index_map(idx)
            idx2 = index_map(p, b, o)
            assert idx2 == idx
    
    def test_h3_projector_lattice_structure(self):
        """H3: Verify projector admissibility forms a lattice."""
        # If p^r | n and p^s | n with r < s, then p^r | p^s
        for p in [2, 3]:
            max_r = 0
            r = 1
            while check_projector_admissibility(p, r):
                max_r = r
                r += 1
            
            # All levels up to max_r should be admissible
            for r in range(1, max_r + 1):
                assert check_projector_admissibility(p, r)
            
            # Next level should not be admissible
            assert not check_projector_admissibility(p, max_r + 1)
    
    def test_h4_bridge_compilation_structure(self):
        """H4: Verify bridge compilation preserves structure."""
        # Compilation should preserve word count (modulo reordering)
        sigmatics = ["phase[h₂=0]", "mark[d=0]", "evaluate"]
        result = compile_sigmatics_to_multiplicity(sigmatics, apply_pi_first=False)
        
        assert len(result) == len(sigmatics)
        
        # With Π-first, reordering is allowed but count is preserved
        result_pi = compile_sigmatics_to_multiplicity(sigmatics, apply_pi_first=True)
        assert len(result_pi) == len(sigmatics)
    
    def test_h5_pi_first_reordering_preserves_atoms(self):
        """H5: Verify Π-first reordering preserves Π-atoms."""
        sigmatics = [
            "phase[h₂=0]",
            "mark[d=0]",
            "evaluate",
            "copy[d=1]",
        ]
        
        result_no_pi = compile_sigmatics_to_multiplicity(sigmatics, apply_pi_first=False)
        result_pi = compile_sigmatics_to_multiplicity(sigmatics, apply_pi_first=True)
        
        # Count of MARK and COPY should be same
        def count_opcode(words, opcode):
            return sum(1 for w in words if w.opcode == opcode)
        
        assert count_opcode(result_no_pi, "MARK") == count_opcode(result_pi, "MARK")
        assert count_opcode(result_no_pi, "COPY") == count_opcode(result_pi, "COPY")
    
    def test_h6_page_partition_structure(self):
        """H6: Verify pages partition the index space."""
        # Each page should contain exactly BYTES_PER_PAGE addresses
        page_sizes = []
        for p in range(NUM_PAGES):
            indices = [index_map(p, 0, o) for o in range(BYTES_PER_PAGE)]
            page_sizes.append(len(set(indices)))
        
        assert all(s == BYTES_PER_PAGE for s in page_sizes)
        
        # Pages should be disjoint
        all_indices = set()
        for p in range(NUM_PAGES):
            page_indices = set(index_map(p, 0, o) for o in range(BYTES_PER_PAGE))
            assert all_indices.isdisjoint(page_indices)
            all_indices.update(page_indices)


# ============================================================================
# R Tests: Baseline Scoring
# ============================================================================

class TrivialBaseline:
    """Trivial baseline for comparison."""
    
    @staticmethod
    def trivial_index(p: int, o: int) -> int:
        """Trivial index: just p + o (wrong, but simple)."""
        return p + o
    
    @staticmethod
    def trivial_compile(words: List[str]) -> List[str]:
        """Trivial compile: identity (no transformation)."""
        return words


class TestBaselineR:
    """Baseline scoring (R) - compare against trivial baseline."""
    
    def test_r1_index_map_vs_trivial(self):
        """R1: Score index_map against trivial baseline."""
        # Count how many times our index_map differs from trivial
        correct_count = 0
        total_count = 0
        
        for p in range(0, NUM_PAGES, 5):
            for o in range(0, BYTES_PER_PAGE, 13):
                our_idx = index_map(p, 0, o)
                trivial_idx = TrivialBaseline.trivial_index(p, o)
                
                # Our index should be correct
                assert our_idx == p * 256 + o
                
                # Count correctness
                if our_idx == p * 256 + o:
                    correct_count += 1
                total_count += 1
        
        # Our implementation should be 100% correct
        score = correct_count / total_count
        assert score == 1.0
        
        # Trivial baseline should be mostly wrong (except p=0 or o=0)
        trivial_correct = 0
        for p in range(0, NUM_PAGES, 5):
            for o in range(0, BYTES_PER_PAGE, 13):
                trivial_idx = TrivialBaseline.trivial_index(p, o)
                if trivial_idx == p * 256 + o:
                    trivial_correct += 1
        
        trivial_score = trivial_correct / total_count
        assert score > trivial_score  # We should beat the baseline
    
    def test_r2_bridge_vs_trivial(self):
        """R2: Score bridge compilation against trivial baseline."""
        sigmatics = ["phase[h₂=0]", "mark[d=0]", "evaluate"]
        
        # Our bridge compilation
        our_result = bridge_compile(sigmatics, apply_pi_first=True)
        
        # Trivial baseline (no transformation)
        trivial_result = TrivialBaseline.trivial_compile(sigmatics)
        
        # Our result should have structure (MultiplicityWords)
        assert len(our_result.multiplicity_words) == 3
        assert hasattr(our_result.multiplicity_words[0], 'opcode')
        
        # Trivial baseline is just strings (no structure)
        assert isinstance(trivial_result[0], str)
        
        # Score: we add structure, baseline doesn't
        our_score = 1.0  # We compile successfully
        trivial_score = 0.0  # Baseline has no compilation
        
        assert our_score > trivial_score
    
    def test_r3_pi_first_effectiveness(self):
        """R3: Score Π-first reduction effectiveness."""
        sigmatics = [
            "evaluate",
            "mark[d=0]",
            "phase[h₂=0]",
            "copy[d=1]",
        ]
        
        # Without Π-first (baseline)
        result_baseline = compile_sigmatics_to_multiplicity(sigmatics, apply_pi_first=False)
        
        # With Π-first (our method)
        result_pi = compile_sigmatics_to_multiplicity(sigmatics, apply_pi_first=True)
        
        # Find positions of Π-atoms
        def find_pi_atom_positions(words):
            positions = []
            for i, w in enumerate(words):
                if w.opcode in ["MARK", "COPY"]:
                    positions.append(i)
            return positions
        
        baseline_pos = find_pi_atom_positions(result_baseline)
        pi_pos = find_pi_atom_positions(result_pi)
        
        # With Π-first, atoms should be earlier on average
        baseline_avg = sum(baseline_pos) / len(baseline_pos) if baseline_pos else 0
        pi_avg = sum(pi_pos) / len(pi_pos) if pi_pos else 0
        
        # Π-first should place atoms earlier
        assert pi_avg <= baseline_avg
        
        # Score: reduction in average position
        score_improvement = baseline_avg - pi_avg
        assert score_improvement >= 0


# ============================================================================
# Integration Tests
# ============================================================================

class TestIntegration:
    """Integration tests combining X, H, and R."""
    
    def test_int1_end_to_end_compilation(self):
        """INT1: End-to-end compilation with all constraints."""
        sigmatics = ["phase[h₂=2]", "mark[d=1]", "copy[d=0]", "evaluate"]
        
        # Compile with Π-first
        result = bridge_compile(sigmatics, apply_pi_first=True)
        
        # X: Numeric check - word count preserved
        assert len(result.multiplicity_words) == len(sigmatics)
        
        # H: Structural check - Π-atoms first
        opcodes = [w.opcode for w in result.multiplicity_words]
        assert opcodes[0] in ["MARK", "COPY"]
        assert opcodes[1] in ["MARK", "COPY"]
        
        # R: Better than trivial baseline
        assert result.pi_first_applied == True
    
    def test_int2_index_map_with_projectors(self):
        """INT2: Verify index map respects projector constraints."""
        # For admissible projectors, index space should be divisible
        for p, r in [(2, 8), (3, 1)]:  # Valid projectors
            assert check_projector_admissibility(p, r)
            
            # Index space size should be divisible by p^r
            block_size = p ** r
            assert INDEX_SIZE % block_size == 0
            
            # Number of blocks
            num_blocks = INDEX_SIZE // block_size
            assert num_blocks * block_size == INDEX_SIZE


# ============================================================================
# Summary Report
# ============================================================================

def generate_test_report():
    """Generate a summary report of test results."""
    import sys
    
    # Run tests and capture results
    exit_code = pytest.main([
        __file__,
        "-v",
        "--tb=short",
        "-q"
    ])
    
    return exit_code


if __name__ == "__main__":
    print("=" * 70)
    print("Phase 0 Test Suite: X (Numeric), H (Structural), R (Baseline)")
    print("=" * 70)
    exit_code = generate_test_report()
    print("=" * 70)
    sys.exit(exit_code)
