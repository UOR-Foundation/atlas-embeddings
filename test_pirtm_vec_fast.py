#!/usr/bin/env python3
"""
Test suite for fast PRNG-based PIRTM k-vector generation.
Tests pirtm_kgen.py and pirtm_adapter_vec_fast.py modules.
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

from atlas.aep import pirtm_kgen, pirtm_adapter_vec_fast


class TestKVectorGeneration:
    """Test fast PRNG-based k vector generation."""
    
    def test_k_vector_size(self):
        """Test k vector has correct size."""
        primes = [2, 3, 5, 7]
        Lambda_m = 503
        alpha = 0.99
        size = 100
        
        k_vec, info = pirtm_kgen.k_vector(size, primes, Lambda_m, alpha)
        
        assert k_vec.shape == (size,)
        assert "seed_hex" in info
        assert "addresses_digest" in info
    
    def test_k_vector_deterministic(self):
        """Test k vector generation is deterministic."""
        primes = [2, 3, 5, 7, 11]
        Lambda_m = 503
        alpha = 0.99
        size = 50
        
        k1, info1 = pirtm_kgen.k_vector(size, primes, Lambda_m, alpha)
        k2, info2 = pirtm_kgen.k_vector(size, primes, Lambda_m, alpha)
        
        np.testing.assert_array_equal(k1, k2)
        assert info1["seed_hex"] == info2["seed_hex"]
    
    def test_k_vector_range(self):
        """Test all k_i are in [0, 1-eps]."""
        primes = [2, 3, 5, 7, 11, 13]
        Lambda_m = 503
        alpha = 0.99
        size = 200
        eps = 1e-3
        
        k_vec, _ = pirtm_kgen.k_vector(size, primes, Lambda_m, alpha, eps=eps)
        
        assert np.all(k_vec >= 0.0)
        assert np.all(k_vec <= 1.0 - eps)
    
    def test_k_vector_alpha_clipping(self):
        """Test alpha clipping to [0, 1-eps]."""
        primes = [2, 3, 5]
        Lambda_m = 503
        size = 100
        eps = 1e-3
        
        # Test alpha > 1
        k_vec, info = pirtm_kgen.k_vector(size, primes, Lambda_m, 1.5, eps=eps)
        assert info["alpha_clipped"] == 1.0 - eps
        assert np.all(k_vec <= 1.0 - eps)
        
        # Test alpha < 0
        k_vec, info = pirtm_kgen.k_vector(size, primes, Lambda_m, -0.5, eps=eps)
        assert info["alpha_clipped"] == 0.0
        assert np.all(k_vec >= 0.0)
    
    def test_k_vector_custom_addresses(self):
        """Test k vector with custom addresses."""
        primes = [2, 3, 5]
        Lambda_m = 503
        alpha = 0.95
        size = 10
        
        # Custom addresses
        custom_addrs = [(i % 96, (i * 10) % 12288) for i in range(size)]
        
        k_vec, info = pirtm_kgen.k_vector(
            size, primes, Lambda_m, alpha, addresses=custom_addrs
        )
        
        assert k_vec.shape == (size,)
        assert "addresses_digest" in info
    
    def test_k_vector_different_inputs_different_output(self):
        """Test different inputs produce different k vectors."""
        Lambda_m = 503
        alpha = 0.99
        size = 50
        
        k1, _ = pirtm_kgen.k_vector(size, [2, 3, 5], Lambda_m, alpha)
        k2, _ = pirtm_kgen.k_vector(size, [2, 3, 7], Lambda_m, alpha)
        
        # Different primes should give different results
        assert not np.array_equal(k1, k2)
    
    def test_k_vector_numpy_backend(self):
        """Test explicit NumPy backend selection."""
        primes = [2, 3, 5, 7]
        Lambda_m = 503
        alpha = 0.99
        size = 100
        
        k_vec, info = pirtm_kgen.k_vector(
            size, primes, Lambda_m, alpha, backend="numpy"
        )
        
        assert k_vec.shape == (size,)
        assert isinstance(k_vec, np.ndarray)
    
    def test_k_vector_variation(self):
        """Test k values have variation (not all the same)."""
        primes = [2, 3, 5, 7]
        Lambda_m = 503
        alpha = 0.99
        size = 100
        
        k_vec, _ = pirtm_kgen.k_vector(size, primes, Lambda_m, alpha)
        
        # Should have variation
        assert len(set(k_vec)) > 1
        assert k_vec.std() > 0.0


class TestAddressesDigest:
    """Test address digest computation."""
    
    def test_addresses_digest_deterministic(self):
        """Test address digest is deterministic."""
        addrs = [(i % 96, i % 12288) for i in range(100)]
        
        d1 = pirtm_kgen._addresses_digest(addrs)
        d2 = pirtm_kgen._addresses_digest(addrs)
        
        assert d1 == d2
    
    def test_addresses_digest_order_matters(self):
        """Test address digest changes with order."""
        addrs1 = [(0, 0), (1, 1), (2, 2)]
        addrs2 = [(2, 2), (1, 1), (0, 0)]
        
        d1 = pirtm_kgen._addresses_digest(addrs1)
        d2 = pirtm_kgen._addresses_digest(addrs2)
        
        assert d1 != d2
    
    def test_addresses_digest_truncation(self):
        """Test address digest truncates large lists."""
        # Create more than 4096 addresses
        addrs_large = [(i % 96, i % 12288) for i in range(5000)]
        addrs_truncated = addrs_large[:4096]
        
        # Digest should be same because it truncates at 4096
        d_large = pirtm_kgen._addresses_digest(addrs_large)
        d_truncated = pirtm_kgen._addresses_digest(addrs_truncated)
        
        assert d_large == d_truncated


class TestSeedMaterial:
    """Test seed material generation."""
    
    def test_seed_material_structure(self):
        """Test seed material has expected structure."""
        primes = [2, 3, 5]
        Lambda_m = 503
        addrs = [(0, 0), (1, 1)]
        
        mat = pirtm_kgen._seed_material(primes, Lambda_m, addrs)
        
        assert "seed_hex" in mat
        assert "addresses_digest" in mat
        assert len(mat["seed_hex"]) == 64  # 32 bytes as hex
    
    def test_seed_material_deterministic(self):
        """Test seed material is deterministic."""
        primes = [2, 3, 5, 7]
        Lambda_m = 503
        addrs = [(i % 96, i % 12288) for i in range(50)]
        
        mat1 = pirtm_kgen._seed_material(primes, Lambda_m, addrs)
        mat2 = pirtm_kgen._seed_material(primes, Lambda_m, addrs)
        
        assert mat1 == mat2


class TestPirtmUpdateVecFast:
    """Test fast vectorized PIRTM update."""
    
    def test_pirtm_update_vec_fast_basic(self):
        """Test basic fast vectorized update."""
        T = np.ones((20,))
        F = np.zeros((20,))
        primes = [2, 3, 5, 7]
        Lambda_m = 503
        alpha = 0.99
        
        T_next, k_vec, proof, info = pirtm_adapter_vec_fast.pirtm_update_vec(
            T, F, primes, Lambda_m, alpha,
            actor_id="test"
        )
        
        assert T_next.shape == T.shape
        assert k_vec.shape == (T.size,)
        assert "k_stats" in info
        assert "seed_hex" in info
        assert "backend" in info
    
    def test_pirtm_update_vec_fast_multidimensional(self):
        """Test fast update with multidimensional arrays."""
        T = np.ones((4, 5))
        F = np.zeros((4, 5))
        primes = [2, 3, 5]
        Lambda_m = 503
        alpha = 0.99
        
        T_next, k_vec, proof, info = pirtm_adapter_vec_fast.pirtm_update_vec(
            T, F, primes, Lambda_m, alpha
        )
        
        assert T_next.shape == (4, 5)
        assert k_vec.shape == (20,)  # Flattened
    
    def test_pirtm_update_vec_fast_deterministic(self):
        """Test fast update is deterministic."""
        T = np.random.randn(30)
        F = np.random.randn(30)
        primes = [2, 3, 5, 7, 11]
        Lambda_m = 503
        alpha = 0.95
        
        T1, k1, proof1, info1 = pirtm_adapter_vec_fast.pirtm_update_vec(
            T, F, primes, Lambda_m, alpha
        )
        T2, k2, proof2, info2 = pirtm_adapter_vec_fast.pirtm_update_vec(
            T, F, primes, Lambda_m, alpha
        )
        
        np.testing.assert_array_equal(T1, T2)
        np.testing.assert_array_equal(k1, k2)
        assert proof1.proof_id == proof2.proof_id
        assert info1["seed_hex"] == info2["seed_hex"]
    
    def test_pirtm_update_vec_fast_shape_mismatch_raises(self):
        """Test ValueError for shape mismatch."""
        T = np.ones((10,))
        F = np.zeros((5,))
        primes = [2, 3, 5]
        Lambda_m = 503
        alpha = 0.99
        
        with pytest.raises(ValueError, match="same shape"):
            pirtm_adapter_vec_fast.pirtm_update_vec(T, F, primes, Lambda_m, alpha)
    
    def test_pirtm_update_vec_fast_k_stats(self):
        """Test k_stats are reasonable."""
        T = np.ones((100,))
        F = np.zeros((100,))
        primes = [2, 3, 5, 7, 11, 13]
        Lambda_m = 503
        alpha = 0.99
        eps = 1e-3
        
        T_next, k_vec, proof, info = pirtm_adapter_vec_fast.pirtm_update_vec(
            T, F, primes, Lambda_m, alpha, eps=eps
        )
        
        stats = info["k_stats"]
        assert 0.0 <= stats["min"] <= 1.0 - eps
        assert 0.0 <= stats["max"] <= 1.0 - eps
        assert stats["min"] <= stats["mean"] <= stats["max"]
        
        # Verify stats match actual k_vec
        np.testing.assert_almost_equal(stats["min"], k_vec.min())
        np.testing.assert_almost_equal(stats["max"], k_vec.max())
        np.testing.assert_almost_equal(stats["mean"], k_vec.mean())
    
    def test_pirtm_update_vec_fast_with_context(self):
        """Test fast update with context information."""
        T = np.ones((10,))
        F = np.zeros((10,))
        primes = [2, 3, 5]
        Lambda_m = 503
        alpha = 0.99
        
        context = {"slot": (1, 2, 3), "note": "test"}
        
        T_next, k_vec, proof, info = pirtm_adapter_vec_fast.pirtm_update_vec(
            T, F, primes, Lambda_m, alpha,
            actor_id="alice",
            context=context
        )
        
        assert proof.kind == "pirtm_update_vec"
        assert "seed_hex" in info
    
    def test_pirtm_update_vec_fast_backend_numpy(self):
        """Test explicit NumPy backend."""
        T = np.ones((50,))
        F = np.zeros((50,))
        primes = [2, 3, 5, 7]
        Lambda_m = 503
        alpha = 0.99
        
        T_next, k_vec, proof, info = pirtm_adapter_vec_fast.pirtm_update_vec(
            T, F, primes, Lambda_m, alpha, backend="numpy"
        )
        
        assert info["backend"] == "numpy"
        assert isinstance(k_vec, np.ndarray)


class TestReverseUpdateVecFast:
    """Test fast vectorized reverse update."""
    
    def test_reverse_update_vec_fast_basic(self):
        """Test reverse update inverts forward update."""
        T = np.random.randn(50)
        F = np.random.randn(50)
        primes = [2, 3, 5, 7]
        Lambda_m = 503
        alpha = 0.95
        
        T_next, k_vec, proof, info = pirtm_adapter_vec_fast.pirtm_update_vec(
            T, F, primes, Lambda_m, alpha
        )
        
        T_recovered = pirtm_adapter_vec_fast.reverse_update_vec(T_next, F, k_vec)
        
        np.testing.assert_allclose(T_recovered, T, rtol=1e-10)
    
    def test_reverse_update_vec_fast_multidimensional(self):
        """Test reverse update with multidimensional arrays."""
        T = np.random.randn(3, 4, 5)
        F = np.random.randn(3, 4, 5)
        primes = [2, 3, 5]
        Lambda_m = 503
        alpha = 0.99
        
        T_next, k_vec, proof, info = pirtm_adapter_vec_fast.pirtm_update_vec(
            T, F, primes, Lambda_m, alpha
        )
        
        T_recovered = pirtm_adapter_vec_fast.reverse_update_vec(T_next, F, k_vec)
        
        assert T_recovered.shape == T.shape
        np.testing.assert_allclose(T_recovered, T, rtol=1e-10)
    
    def test_reverse_update_vec_fast_shape_mismatch_raises(self):
        """Test ValueError for shape mismatch."""
        T_next = np.ones((10,))
        F = np.zeros((5,))
        k_vec = np.ones((10,))
        
        with pytest.raises(ValueError, match="shape mismatch"):
            pirtm_adapter_vec_fast.reverse_update_vec(T_next, F, k_vec)
    
    def test_reverse_update_vec_fast_kvec_size_mismatch_raises(self):
        """Test ValueError for k_vec size mismatch."""
        T_next = np.ones((10,))
        F = np.zeros((10,))
        k_vec = np.ones((5,))
        
        with pytest.raises(ValueError, match="k_vec size mismatch"):
            pirtm_adapter_vec_fast.reverse_update_vec(T_next, F, k_vec)


class TestIntegration:
    """Integration tests for fast PIRTM."""
    
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
        T_next, k_vec, proof, info = pirtm_adapter_vec_fast.pirtm_update_vec(
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
        assert "seed_hex" in info
        assert len(info["k_first"]) == 8
        
        # Reverse
        T_recovered = pirtm_adapter_vec_fast.reverse_update_vec(T_next, F, k_vec)
        
        # Check reversibility
        assert np.linalg.norm(T_recovered - T) < 1e-10
    
    def test_consistency_same_seed(self):
        """Test multiple calls with same inputs produce same results."""
        T = np.random.randn(200)
        F = np.random.randn(200)
        primes = [2, 3, 5, 7, 11]
        Lambda_m = 503
        alpha = 0.95
        
        results = []
        for _ in range(3):
            T_next, k_vec, proof, info = pirtm_adapter_vec_fast.pirtm_update_vec(
                T, F, primes, Lambda_m, alpha
            )
            results.append((T_next, k_vec, proof.proof_id, info["seed_hex"]))
        
        # All results should be identical
        for i in range(1, len(results)):
            np.testing.assert_array_equal(results[0][0], results[i][0])
            np.testing.assert_array_equal(results[0][1], results[i][1])
            assert results[0][2] == results[i][2]
            assert results[0][3] == results[i][3]
    
    def test_different_backends_same_seed(self):
        """Test NumPy backend produces consistent results."""
        T = np.random.randn(100)
        F = np.random.randn(100)
        primes = [2, 3, 5, 7]
        Lambda_m = 503
        alpha = 0.95
        
        # NumPy backend (explicit)
        T1, k1, proof1, info1 = pirtm_adapter_vec_fast.pirtm_update_vec(
            T, F, primes, Lambda_m, alpha, backend="numpy"
        )
        
        # NumPy backend (default)
        T2, k2, proof2, info2 = pirtm_adapter_vec_fast.pirtm_update_vec(
            T, F, primes, Lambda_m, alpha
        )
        
        # Should produce identical results
        np.testing.assert_array_equal(T1, T2)
        np.testing.assert_array_equal(k1, k2)
        assert info1["seed_hex"] == info2["seed_hex"]


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
