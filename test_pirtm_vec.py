#!/usr/bin/env python3
"""
Test suite for vectorized PIRTM functionality.
Tests pirtm_merkle.py and pirtm_adapter_vec.py modules.
"""
from __future__ import annotations

import sys
from pathlib import Path

# Ensure we import real numpy by removing repo root from path first
_repo_root = str(Path(__file__).parent)
_saved_path = sys.path[:]
sys.path = [p for p in sys.path if not p.endswith('atlas-hologram') and _repo_root not in p]

# Import real numpy from site-packages
import numpy as np
import pytest

# Restore path and add atlas/aep
sys.path = _saved_path
sys.path.insert(0, str(Path(__file__).parent / "atlas" / "aep"))

from atlas.aep import pirtm_merkle, pirtm_adapter_vec


class TestMerkleTree:
    """Test Merkle tree functionality."""
    
    def test_leaf_hash_deterministic(self):
        """Test leaf hash is deterministic."""
        item = {"key": "value", "num": 42}
        h1 = pirtm_merkle.leaf_hash(item)
        h2 = pirtm_merkle.leaf_hash(item)
        assert h1 == h2
    
    def test_leaf_hash_different_items(self):
        """Test different items produce different hashes."""
        item1 = {"key": "value1"}
        item2 = {"key": "value2"}
        h1 = pirtm_merkle.leaf_hash(item1)
        h2 = pirtm_merkle.leaf_hash(item2)
        assert h1 != h2
    
    def test_merkle_root_empty(self):
        """Test Merkle root of empty list."""
        root = pirtm_merkle.merkle_root([])
        assert isinstance(root, str)
        assert len(root) == 64  # 32 bytes as hex
    
    def test_merkle_root_single_item(self):
        """Test Merkle root of single item equals leaf hash."""
        item = {"key": "value"}
        root = pirtm_merkle.merkle_root([item])
        leaf = pirtm_merkle.leaf_hash(item)
        assert root == leaf
    
    def test_merkle_root_deterministic(self):
        """Test Merkle root is deterministic."""
        items = [{"i": i} for i in range(10)]
        root1 = pirtm_merkle.merkle_root(items)
        root2 = pirtm_merkle.merkle_root(items)
        assert root1 == root2
    
    def test_merkle_root_order_matters(self):
        """Test Merkle root changes with different order."""
        items1 = [{"i": 0}, {"i": 1}]
        items2 = [{"i": 1}, {"i": 0}]
        root1 = pirtm_merkle.merkle_root(items1)
        root2 = pirtm_merkle.merkle_root(items2)
        assert root1 != root2
    
    def test_merkle_proof_and_verify(self):
        """Test Merkle proof generation and verification."""
        items = [{"i": i, "data": f"item_{i}"} for i in range(16)]
        root = pirtm_merkle.merkle_root(items)
        
        # Test proof for various indices
        for idx in [0, 5, 10, 15]:
            proof = pirtm_merkle.merkle_proof(items, idx)
            assert pirtm_merkle.merkle_verify(root, items[idx], idx, proof)
    
    def test_merkle_verify_wrong_item(self):
        """Test verification fails for wrong item."""
        items = [{"i": i} for i in range(8)]
        root = pirtm_merkle.merkle_root(items)
        proof = pirtm_merkle.merkle_proof(items, 3)
        
        wrong_item = {"i": 999}
        assert not pirtm_merkle.merkle_verify(root, wrong_item, 3, proof)
    
    def test_merkle_verify_wrong_index(self):
        """Test verification fails for wrong index."""
        items = [{"i": i} for i in range(8)]
        root = pirtm_merkle.merkle_root(items)
        proof = pirtm_merkle.merkle_proof(items, 3)
        
        # Use correct item but wrong index
        assert not pirtm_merkle.merkle_verify(root, items[3], 5, proof)
    
    def test_merkle_proof_odd_length(self):
        """Test Merkle proof works with odd-length lists."""
        items = [{"i": i} for i in range(7)]
        root = pirtm_merkle.merkle_root(items)
        
        for idx in range(len(items)):
            proof = pirtm_merkle.merkle_proof(items, idx)
            assert pirtm_merkle.merkle_verify(root, items[idx], idx, proof)


class TestDefaultAddressMap:
    """Test default address mapping."""
    
    def test_address_map_size(self):
        """Test address map returns correct size."""
        size = 100
        addrs = pirtm_adapter_vec.default_address_map(size)
        assert len(addrs) == size
    
    def test_address_map_deterministic(self):
        """Test address map is deterministic."""
        size = 50
        addrs1 = pirtm_adapter_vec.default_address_map(size)
        addrs2 = pirtm_adapter_vec.default_address_map(size)
        assert addrs1 == addrs2
    
    def test_address_map_range(self):
        """Test addresses are in valid ranges."""
        size = 1000
        addrs = pirtm_adapter_vec.default_address_map(size)
        
        for class_idx, coord_idx in addrs:
            assert 0 <= class_idx < pirtm_adapter_vec.NUM_CLASSES
            assert 0 <= coord_idx < pirtm_adapter_vec.NUM_COORDS
    
    def test_address_map_pattern(self):
        """Test address mapping follows expected pattern."""
        addrs = pirtm_adapter_vec.default_address_map(200)
        
        # First 96 should cycle through classes 0-95
        for i in range(96):
            assert addrs[i][0] == i
            assert addrs[i][1] == 0
        
        # Next 96 should cycle through classes again with coord=1
        for i in range(96, 192):
            assert addrs[i][0] == (i % 96)
            assert addrs[i][1] == 1


class TestDeriveKVector:
    """Test vectorized k derivation."""
    
    def test_derive_k_vector_size(self):
        """Test k vector has correct size."""
        primes = [2, 3, 5, 7]
        Lambda_m = 503
        alpha = 0.99
        size = 100
        
        k_vec, addrs, meta = pirtm_adapter_vec.derive_k_vector(
            primes, Lambda_m, alpha, size
        )
        
        assert k_vec.shape == (size,)
        assert len(addrs) == size
    
    def test_derive_k_vector_deterministic(self):
        """Test k vector derivation is deterministic."""
        primes = [2, 3, 5, 7, 11]
        Lambda_m = 503
        alpha = 0.99
        size = 50
        
        k1, addrs1, meta1 = pirtm_adapter_vec.derive_k_vector(
            primes, Lambda_m, alpha, size
        )
        k2, addrs2, meta2 = pirtm_adapter_vec.derive_k_vector(
            primes, Lambda_m, alpha, size
        )
        
        np.testing.assert_array_equal(k1, k2)
        assert addrs1 == addrs2
    
    def test_derive_k_vector_range(self):
        """Test all k_i are in [0, 1-eps]."""
        primes = [2, 3, 5, 7, 11, 13]
        Lambda_m = 503
        alpha = 0.99
        size = 200
        eps = 1e-3
        
        k_vec, _, _ = pirtm_adapter_vec.derive_k_vector(
            primes, Lambda_m, alpha, size, eps=eps
        )
        
        assert np.all(k_vec >= 0.0)
        assert np.all(k_vec < 1.0 - eps)
    
    def test_derive_k_vector_custom_addresses(self):
        """Test k vector with custom addresses."""
        primes = [2, 3, 5]
        Lambda_m = 503
        alpha = 0.95
        size = 10
        
        # Custom addresses
        custom_addrs = [(i % 96, (i * 10) % 12288) for i in range(size)]
        
        k_vec, addrs, meta = pirtm_adapter_vec.derive_k_vector(
            primes, Lambda_m, alpha, size, addresses=custom_addrs
        )
        
        assert addrs == custom_addrs
        assert k_vec.shape == (size,)
    
    def test_derive_k_vector_addresses_mismatch_raises(self):
        """Test ValueError for mismatched addresses length."""
        primes = [2, 3, 5]
        Lambda_m = 503
        alpha = 0.95
        size = 10
        
        wrong_addrs = [(0, 0)] * 5  # Only 5 addresses for size 10
        
        with pytest.raises(ValueError, match="addresses length"):
            pirtm_adapter_vec.derive_k_vector(
                primes, Lambda_m, alpha, size, addresses=wrong_addrs
            )
    
    def test_derive_k_vector_varies_per_coordinate(self):
        """Test k values vary across coordinates."""
        primes = [2, 3, 5, 7]
        Lambda_m = 503
        alpha = 0.99
        size = 100
        
        k_vec, _, _ = pirtm_adapter_vec.derive_k_vector(
            primes, Lambda_m, alpha, size
        )
        
        # Should have variation (not all the same)
        assert len(set(k_vec)) > 1
        assert k_vec.std() > 0.0


class TestPirtmUpdateVec:
    """Test vectorized PIRTM update."""
    
    def test_pirtm_update_vec_basic(self):
        """Test basic vectorized update."""
        T = np.ones((20,))
        F = np.zeros((20,))
        primes = [2, 3, 5, 7]
        Lambda_m = 503
        alpha = 0.99
        
        T_next, k_vec, proof, info = pirtm_adapter_vec.pirtm_update_vec(
            T, F, primes, Lambda_m, alpha,
            actor_id="test"
        )
        
        assert T_next.shape == T.shape
        assert k_vec.shape == (T.size,)
        assert "k_stats" in info
        assert "bindings_root" in info
    
    def test_pirtm_update_vec_multidimensional(self):
        """Test vectorized update with multidimensional arrays."""
        T = np.ones((4, 5))
        F = np.zeros((4, 5))
        primes = [2, 3, 5]
        Lambda_m = 503
        alpha = 0.99
        
        T_next, k_vec, proof, info = pirtm_adapter_vec.pirtm_update_vec(
            T, F, primes, Lambda_m, alpha
        )
        
        assert T_next.shape == (4, 5)
        assert k_vec.shape == (20,)  # Flattened
    
    def test_pirtm_update_vec_deterministic(self):
        """Test vectorized update is deterministic."""
        T = np.random.randn(30)
        F = np.random.randn(30)
        primes = [2, 3, 5, 7, 11]
        Lambda_m = 503
        alpha = 0.95
        
        T1, k1, proof1, info1 = pirtm_adapter_vec.pirtm_update_vec(
            T, F, primes, Lambda_m, alpha
        )
        T2, k2, proof2, info2 = pirtm_adapter_vec.pirtm_update_vec(
            T, F, primes, Lambda_m, alpha
        )
        
        np.testing.assert_array_equal(T1, T2)
        np.testing.assert_array_equal(k1, k2)
        assert proof1.proof_id == proof2.proof_id
    
    def test_pirtm_update_vec_shape_mismatch_raises(self):
        """Test ValueError for shape mismatch."""
        T = np.ones((10,))
        F = np.zeros((5,))
        primes = [2, 3, 5]
        Lambda_m = 503
        alpha = 0.99
        
        with pytest.raises(ValueError, match="same shape"):
            pirtm_adapter_vec.pirtm_update_vec(T, F, primes, Lambda_m, alpha)
    
    def test_pirtm_update_vec_k_stats(self):
        """Test k_stats are reasonable."""
        T = np.ones((100,))
        F = np.zeros((100,))
        primes = [2, 3, 5, 7, 11, 13]
        Lambda_m = 503
        alpha = 0.99
        eps = 1e-3
        
        T_next, k_vec, proof, info = pirtm_adapter_vec.pirtm_update_vec(
            T, F, primes, Lambda_m, alpha, eps=eps
        )
        
        stats = info["k_stats"]
        assert 0.0 <= stats["min"] < 1.0 - eps
        assert 0.0 <= stats["max"] < 1.0 - eps
        assert stats["min"] <= stats["mean"] <= stats["max"]
        
        # Verify stats match actual k_vec
        np.testing.assert_almost_equal(stats["min"], k_vec.min())
        np.testing.assert_almost_equal(stats["max"], k_vec.max())
        np.testing.assert_almost_equal(stats["mean"], k_vec.mean())
    
    def test_pirtm_update_vec_with_context(self):
        """Test update with context information."""
        T = np.ones((10,))
        F = np.zeros((10,))
        primes = [2, 3, 5]
        Lambda_m = 503
        alpha = 0.99
        
        context = {"slot": (1, 2, 3), "note": "test"}
        
        T_next, k_vec, proof, info = pirtm_adapter_vec.pirtm_update_vec(
            T, F, primes, Lambda_m, alpha,
            actor_id="alice",
            context=context
        )
        
        assert proof.kind == "pirtm_update_vec"


class TestReverseUpdateVec:
    """Test vectorized reverse update."""
    
    def test_reverse_update_vec_basic(self):
        """Test reverse update inverts forward update."""
        T = np.random.randn(50)
        F = np.random.randn(50)
        primes = [2, 3, 5, 7]
        Lambda_m = 503
        alpha = 0.95
        
        T_next, k_vec, proof, info = pirtm_adapter_vec.pirtm_update_vec(
            T, F, primes, Lambda_m, alpha
        )
        
        T_recovered = pirtm_adapter_vec.reverse_update_vec(T_next, F, k_vec)
        
        np.testing.assert_allclose(T_recovered, T, rtol=1e-10)
    
    def test_reverse_update_vec_multidimensional(self):
        """Test reverse update with multidimensional arrays."""
        T = np.random.randn(3, 4, 5)
        F = np.random.randn(3, 4, 5)
        primes = [2, 3, 5]
        Lambda_m = 503
        alpha = 0.99
        
        T_next, k_vec, proof, info = pirtm_adapter_vec.pirtm_update_vec(
            T, F, primes, Lambda_m, alpha
        )
        
        T_recovered = pirtm_adapter_vec.reverse_update_vec(T_next, F, k_vec)
        
        assert T_recovered.shape == T.shape
        np.testing.assert_allclose(T_recovered, T, rtol=1e-10)
    
    def test_reverse_update_vec_shape_mismatch_raises(self):
        """Test ValueError for shape mismatch."""
        T_next = np.ones((10,))
        F = np.zeros((5,))
        k_vec = np.ones((10,))
        
        with pytest.raises(ValueError, match="shape mismatch"):
            pirtm_adapter_vec.reverse_update_vec(T_next, F, k_vec)
    
    def test_reverse_update_vec_kvec_size_mismatch_raises(self):
        """Test ValueError for k_vec size mismatch."""
        T_next = np.ones((10,))
        F = np.zeros((10,))
        k_vec = np.ones((5,))
        
        with pytest.raises(ValueError, match="k_vec size mismatch"):
            pirtm_adapter_vec.reverse_update_vec(T_next, F, k_vec)
    
    def test_reverse_update_vec_different_kvec(self):
        """Test reverse with different k vectors gives different results."""
        T_next = np.ones((20,))
        F = np.zeros((20,))
        k_vec1 = np.full((20,), 0.5)
        k_vec2 = np.full((20,), 0.8)
        
        T1 = pirtm_adapter_vec.reverse_update_vec(T_next, F, k_vec1)
        T2 = pirtm_adapter_vec.reverse_update_vec(T_next, F, k_vec2)
        
        # Results should be different
        assert not np.allclose(T1, T2)


class TestIntegration:
    """Integration tests for vectorized PIRTM."""
    
    def test_full_workflow(self):
        """Test complete workflow: update, proof, reverse."""
        # Setup
        d = 96 * 8
        T = np.arange(d, dtype=float)
        F = np.zeros_like(T)
        primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
        Lambda_m = 503
        alpha = 0.95
        
        # Update
        T_next, k_vec, proof, info = pirtm_adapter_vec.pirtm_update_vec(
            T, F, primes, Lambda_m, alpha,
            actor_id="atlas",
            context={"demo": True}
        )
        
        # Verify proof structure
        assert proof.kind == "pirtm_update_vec"
        assert len(proof.proof_id) == 64  # hex string
        
        # Verify info structure
        assert "k_stats" in info
        assert "bindings_root" in info
        assert "addresses_preview" in info
        assert len(info["k_first"]) == 8
        
        # Reverse
        T_recovered = pirtm_adapter_vec.reverse_update_vec(T_next, F, k_vec)
        
        # Check reversibility
        assert np.linalg.norm(T_recovered - T) < 1e-10
    
    def test_merkle_commitment_integration(self):
        """Test Merkle commitments are properly generated."""
        T = np.ones((100,))
        F = np.zeros((100,))
        primes = [2, 3, 5, 7, 11]
        Lambda_m = 503
        alpha = 0.99
        
        T_next, k_vec, proof, info = pirtm_adapter_vec.pirtm_update_vec(
            T, F, primes, Lambda_m, alpha
        )
        
        # Verify Merkle root is present
        assert "bindings_root" in info
        assert isinstance(info["bindings_root"], str)
        assert len(info["bindings_root"]) == 64
        
        # Verify bindings preview
        assert "bindings_preview" in info
        assert len(info["bindings_preview"]) <= 8
        for b in info["bindings_preview"]:
            assert "p" in b
            assert "class" in b
            assert "coord" in b


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
