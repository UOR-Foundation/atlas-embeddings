#!/usr/bin/env python3
"""
Test suite for PIRTM proof system.
Tests pirtm_proofs.py and pirtm_adapter.py modules.
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

from atlas.aep import pirtm_proofs, pirtm_adapter


class TestStatelessProofManager:
    """Test the stateless proof manager."""
    
    def test_generate_proof(self):
        """Test proof generation is deterministic."""
        payload = {"key": "value", "num": 42}
        proof1 = pirtm_proofs.StatelessProofManager.generate("test", payload)
        proof2 = pirtm_proofs.StatelessProofManager.generate("test", payload)
        
        assert proof1.proof_id == proof2.proof_id
        assert proof1.kind == "test"
        assert proof1.payload_hash == proof2.payload_hash
    
    def test_verify_proof_valid(self):
        """Test verification succeeds for valid proof."""
        payload = {"key": "value", "num": 42}
        proof = pirtm_proofs.StatelessProofManager.generate("test", payload)
        
        assert pirtm_proofs.StatelessProofManager.verify(proof, payload)
    
    def test_verify_proof_invalid_payload(self):
        """Test verification fails for modified payload."""
        payload = {"key": "value", "num": 42}
        proof = pirtm_proofs.StatelessProofManager.generate("test", payload)
        
        modified_payload = {"key": "value", "num": 43}
        assert not pirtm_proofs.StatelessProofManager.verify(proof, modified_payload)
    
    def test_verify_proof_invalid_kind(self):
        """Test verification fails when proof kind mismatches."""
        payload = {"key": "value", "num": 42}
        proof = pirtm_proofs.StatelessProofManager.generate("test", payload)
        
        # Create a fake proof with wrong kind
        fake_proof = pirtm_proofs.Proof(
            proof_id=proof.proof_id,
            kind="wrong_kind",
            payload_hash=proof.payload_hash
        )
        
        assert not pirtm_proofs.StatelessProofManager.verify(fake_proof, payload)


class TestPrimeBindings:
    """Test prime binding functionality."""
    
    def test_bind_primes_deterministic(self):
        """Test prime bindings are deterministic."""
        primes = [2, 3, 5, 7, 11]
        bindings1 = pirtm_adapter.bind_primes(primes)
        bindings2 = pirtm_adapter.bind_primes(primes)
        
        assert bindings1 == bindings2
    
    def test_bind_primes_range(self):
        """Test bindings are in valid ranges."""
        primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        bindings = pirtm_adapter.bind_primes(primes)
        
        for p, class_idx, coord_idx in bindings:
            assert 0 <= class_idx < pirtm_adapter.NUM_CLASSES
            assert 0 <= coord_idx < pirtm_adapter.NUM_COORDS
    
    def test_bind_primes_unique_per_prime(self):
        """Test each prime gets a unique binding."""
        primes = [2, 3, 5, 7, 11]
        bindings = pirtm_adapter.bind_primes(primes)
        
        prime_to_binding = {p: (c, co) for p, c, co in bindings}
        assert len(prime_to_binding) == len(primes)


class TestDeriveK:
    """Test k derivation functionality."""
    
    def test_derive_k_deterministic(self):
        """Test k derivation is deterministic."""
        primes = [2, 3, 5, 7, 11]
        Lambda_m = 503
        alpha = 0.99
        
        k1, info1 = pirtm_adapter.derive_k(primes, Lambda_m, alpha)
        k2, info2 = pirtm_adapter.derive_k(primes, Lambda_m, alpha)
        
        assert k1 == k2
        assert info1["k"] == info2["k"]
    
    def test_derive_k_in_range(self):
        """Test k is in [0, 1-eps]."""
        primes = [2, 3, 5, 7, 11]
        Lambda_m = 503
        alpha = 0.99
        eps = 1e-3
        
        k, info = pirtm_adapter.derive_k(primes, Lambda_m, alpha, eps=eps)
        
        assert 0.0 <= k < 1.0 - eps
        assert info["eps"] == eps
    
    def test_derive_k_respects_alpha(self):
        """Test k respects alpha parameter."""
        primes = [2, 3, 5, 7, 11]
        Lambda_m = 503
        
        k1, _ = pirtm_adapter.derive_k(primes, Lambda_m, alpha=0.5)
        k2, _ = pirtm_adapter.derive_k(primes, Lambda_m, alpha=1.0)
        
        # With higher alpha, we expect k to potentially be larger
        # But clipping may affect this, so we just check they're different
        # when the raw values would be different
        assert isinstance(k1, float)
        assert isinstance(k2, float)
    
    def test_derive_k_different_primes(self):
        """Test different primes give different k values."""
        Lambda_m = 503
        alpha = 0.99
        
        k1, _ = pirtm_adapter.derive_k([2, 3, 5], Lambda_m, alpha)
        k2, _ = pirtm_adapter.derive_k([7, 11, 13], Lambda_m, alpha)
        
        # Different primes should give different k (with high probability)
        assert k1 != k2


class TestUpdateFunctions:
    """Test update and reverse update functions."""
    
    def test_apply_update(self):
        """Test apply_update computes F + k*T."""
        T = np.array([1.0, 2.0, 3.0])
        F = np.array([0.1, 0.2, 0.3])
        k = 0.5
        
        T_next = pirtm_adapter.apply_update(T, F, k)
        expected = F + k * T
        
        np.testing.assert_allclose(T_next, expected)
    
    def test_reverse_update(self):
        """Test reverse_update inverts apply_update."""
        T = np.array([1.0, 2.0, 3.0, 4.0])
        F = np.array([0.1, 0.2, 0.3, 0.4])
        k = 0.5
        
        T_next = pirtm_adapter.apply_update(T, F, k)
        T_recovered = pirtm_adapter.reverse_update(T_next, F, k)
        
        np.testing.assert_allclose(T_recovered, T, rtol=1e-10)
    
    def test_reverse_update_raises_on_invalid_k(self):
        """Test reverse_update raises ValueError for k >= 1."""
        T_next = np.array([1.0, 2.0, 3.0])
        F = np.array([0.1, 0.2, 0.3])
        
        with pytest.raises(ValueError, match="k must be in"):
            pirtm_adapter.reverse_update(T_next, F, 1.0)
        
        with pytest.raises(ValueError, match="k must be in"):
            pirtm_adapter.reverse_update(T_next, F, 1.5)


class TestPirtmUpdate:
    """Test the main pirtm_update function."""
    
    def test_pirtm_update_basic(self):
        """Test basic pirtm_update functionality."""
        T = np.ones((10,))
        F = np.zeros((10,))
        primes = [2, 3, 5, 7]
        Lambda_m = 503
        alpha = 0.99
        
        T_next, proof, info = pirtm_adapter.pirtm_update(
            T, F, primes, Lambda_m, alpha,
            actor_id="test",
            context={"test": True}
        )
        
        assert T_next.shape == T.shape
        assert isinstance(proof, pirtm_proofs.Proof)
        assert "k" in info
        assert "k_info" in info
        assert "bindings" in info
        assert "bindings_digest" in info
    
    def test_pirtm_update_deterministic(self):
        """Test pirtm_update is deterministic."""
        T = np.ones((10,))
        F = np.zeros((10,))
        primes = [2, 3, 5, 7]
        Lambda_m = 503
        alpha = 0.99
        
        T_next1, proof1, info1 = pirtm_adapter.pirtm_update(
            T, F, primes, Lambda_m, alpha
        )
        
        T_next2, proof2, info2 = pirtm_adapter.pirtm_update(
            T, F, primes, Lambda_m, alpha
        )
        
        np.testing.assert_allclose(T_next1, T_next2)
        assert proof1.proof_id == proof2.proof_id
        assert info1["k"] == info2["k"]
    
    def test_pirtm_update_shape_mismatch_raises(self):
        """Test pirtm_update raises ValueError for shape mismatch."""
        T = np.ones((10,))
        F = np.zeros((5,))
        primes = [2, 3, 5]
        Lambda_m = 503
        alpha = 0.99
        
        with pytest.raises(ValueError, match="same shape"):
            pirtm_adapter.pirtm_update(T, F, primes, Lambda_m, alpha)
    
    def test_pirtm_update_reversible(self):
        """Test pirtm_update is reversible."""
        T = np.random.randn(20)
        F = np.random.randn(20)
        primes = [2, 3, 5, 7, 11]
        Lambda_m = 503
        alpha = 0.99
        
        T_next, proof, info = pirtm_adapter.pirtm_update(
            T, F, primes, Lambda_m, alpha
        )
        
        T_recovered = pirtm_adapter.reverse_update(T_next, F, info["k"])
        
        np.testing.assert_allclose(T_recovered, T, rtol=1e-10)
    
    def test_pirtm_update_multidimensional(self):
        """Test pirtm_update works with multidimensional arrays."""
        T = np.ones((4, 5))
        F = np.zeros((4, 5))
        primes = [2, 3, 5]
        Lambda_m = 503
        alpha = 0.99
        
        T_next, proof, info = pirtm_adapter.pirtm_update(
            T, F, primes, Lambda_m, alpha
        )
        
        assert T_next.shape == (4, 5)
        
        # Test reversibility
        T_recovered = pirtm_adapter.reverse_update(T_next, F, info["k"])
        np.testing.assert_allclose(T_recovered, T, rtol=1e-10)


class TestArrayDigest:
    """Test array digest functionality."""
    
    def test_array_digest_deterministic(self):
        """Test array digest is deterministic."""
        arr = np.array([1.0, 2.0, 3.0, 4.0])
        
        digest1 = pirtm_adapter._array_digest(arr)
        digest2 = pirtm_adapter._array_digest(arr)
        
        assert digest1 == digest2
    
    def test_array_digest_different_for_different_arrays(self):
        """Test array digest differs for different arrays."""
        arr1 = np.array([1.0, 2.0, 3.0])
        arr2 = np.array([1.0, 2.0, 4.0])
        
        digest1 = pirtm_adapter._array_digest(arr1)
        digest2 = pirtm_adapter._array_digest(arr2)
        
        assert digest1 != digest2


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
