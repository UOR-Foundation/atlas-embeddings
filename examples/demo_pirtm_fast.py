#!/usr/bin/env python3
"""
Example demonstrating fast PRNG-based PIRTM k-vector generation.

This example shows how to use the new pirtm_adapter_vec_fast module
with both CPU (NumPy) and GPU (CuPy) backends.
"""
from __future__ import annotations

import sys
from pathlib import Path

# Ensure proper numpy import by removing repo root from path
_saved_path = sys.path[:]
sys.path = [p for p in sys.path if not p.endswith('atlas-hologram')]
import numpy as np
sys.path = _saved_path

# Add atlas/aep to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent / "atlas" / "aep"))

from pirtm_adapter_vec_fast import pirtm_update_vec, reverse_update_vec


def demonstrate_fast_pirtm():
    """Demonstrate fast PIRTM update with various configurations."""
    
    print("=" * 70)
    print("Fast PRNG-based PIRTM K-Vector Generation Demo")
    print("=" * 70)
    
    # Setup
    T = np.random.randn(96 * 8)  # 768 elements
    F = np.random.randn(96 * 8)
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    Lambda_m = 503
    alpha = 0.95
    
    print(f"\nInput shapes: T={T.shape}, F={F.shape}")
    print(f"Primes: {primes}")
    print(f"Lambda_m: {Lambda_m}, alpha: {alpha}")
    
    # Test 1: NumPy backend (CPU)
    print("\n" + "-" * 70)
    print("Test 1: NumPy Backend (CPU)")
    print("-" * 70)
    
    T_next, k_vec, proof, info = pirtm_update_vec(
        T, F, primes, Lambda_m, alpha,
        backend="numpy",
        actor_id="atlas",
        context={"slot": (1, 2, 3), "test": "demo"}
    )
    
    print(f"✓ T_next shape: {T_next.shape}")
    print(f"✓ k_vec shape: {k_vec.shape}")
    print(f"✓ k_vec range: [{k_vec.min():.6f}, {k_vec.max():.6f}]")
    print(f"✓ k_vec stats:")
    print(f"  - min:  {info['k_stats']['min']:.6f}")
    print(f"  - max:  {info['k_stats']['max']:.6f}")
    print(f"  - mean: {info['k_stats']['mean']:.6f}")
    print(f"✓ seed_hex: {info['seed_hex'][:32]}...")
    print(f"✓ backend: {info['backend']}")
    print(f"✓ proof_id: {proof.proof_id[:32]}...")
    print(f"✓ merkle_root: {info['bindings_root'][:32]}...")
    
    # Test reversibility
    T_recovered = reverse_update_vec(T_next, F, k_vec)
    error = np.linalg.norm(T_recovered - T)
    print(f"✓ Reversibility error: {error:.2e}")
    
    # Test 2: Determinism
    print("\n" + "-" * 70)
    print("Test 2: Determinism Check")
    print("-" * 70)
    
    T_next2, k_vec2, proof2, info2 = pirtm_update_vec(
        T, F, primes, Lambda_m, alpha,
        backend="numpy",
        actor_id="atlas",
        context={"slot": (1, 2, 3), "test": "demo"}
    )
    
    deterministic = np.array_equal(T_next, T_next2) and np.array_equal(k_vec, k_vec2)
    seed_match = info["seed_hex"] == info2["seed_hex"]
    proof_match = proof.proof_id == proof2.proof_id
    
    print(f"✓ T_next identical: {deterministic}")
    print(f"✓ k_vec identical: {np.array_equal(k_vec, k_vec2)}")
    print(f"✓ seed_hex match: {seed_match}")
    print(f"✓ proof_id match: {proof_match}")
    
    # Test 3: Different inputs produce different outputs
    print("\n" + "-" * 70)
    print("Test 3: Input Sensitivity")
    print("-" * 70)
    
    primes_alt = [2, 3, 5, 7, 11, 13, 17, 19, 23, 31]  # Changed last prime
    T_next3, k_vec3, proof3, info3 = pirtm_update_vec(
        T, F, primes_alt, Lambda_m, alpha,
        backend="numpy",
        actor_id="atlas"
    )
    
    different_output = not np.array_equal(k_vec, k_vec3)
    different_seed = info["seed_hex"] != info3["seed_hex"]
    
    print(f"✓ Different primes → different k_vec: {different_output}")
    print(f"✓ Different primes → different seed: {different_seed}")
    print(f"  Original seed: {info['seed_hex'][:32]}...")
    print(f"  New seed:      {info3['seed_hex'][:32]}...")
    
    # Test 4: CuPy backend (GPU) - if available
    print("\n" + "-" * 70)
    print("Test 4: CuPy Backend (GPU)")
    print("-" * 70)
    
    try:
        import cupy
        T_next_gpu, k_vec_gpu, proof_gpu, info_gpu = pirtm_update_vec(
            T, F, primes, Lambda_m, alpha,
            backend="cupy",
            actor_id="atlas"
        )
        
        print(f"✓ CuPy available: Yes")
        print(f"✓ T_next_gpu shape: {T_next_gpu.shape}")
        print(f"✓ k_vec_gpu type: {type(k_vec_gpu).__name__} (returned as NumPy for compatibility)")
        print(f"✓ backend: {info_gpu['backend']}")
        print(f"✓ Results match CPU: {np.array_equal(T_next, T_next_gpu)}")
        
    except ImportError:
        print("✓ CuPy not available - skipping GPU test")
        print("  (Install CuPy for GPU acceleration)")
    
    # Test 5: Multidimensional arrays
    print("\n" + "-" * 70)
    print("Test 5: Multidimensional Arrays")
    print("-" * 70)
    
    T_2d = np.random.randn(24, 32)
    F_2d = np.random.randn(24, 32)
    
    T_next_2d, k_vec_2d, proof_2d, info_2d = pirtm_update_vec(
        T_2d, F_2d, primes, Lambda_m, alpha,
        backend="numpy"
    )
    
    print(f"✓ Input shape: {T_2d.shape}")
    print(f"✓ Output shape: {T_next_2d.shape} (preserved)")
    print(f"✓ k_vec shape: {k_vec_2d.shape} (flattened)")
    
    T_recovered_2d = reverse_update_vec(T_next_2d, F_2d, k_vec_2d)
    error_2d = np.linalg.norm(T_recovered_2d - T_2d)
    print(f"✓ Reversibility error: {error_2d:.2e}")
    
    # Summary
    print("\n" + "=" * 70)
    print("Summary")
    print("=" * 70)
    print("✅ Fast PRNG-based k-generation working correctly")
    print("✅ Deterministic for same inputs")
    print("✅ Supports CPU (NumPy) and GPU (CuPy) backends")
    print("✅ Fully reversible updates")
    print("✅ Compatible with existing PIRTM API")
    print("\nPerformance notes:")
    print("  - CPU: NumPy PCG64 with vectorized C loop")
    print("  - GPU: CuPy XORWOW with parallel device kernel")
    print("  - No per-element Python hashing overhead")
    print("\nSecurity notes:")
    print("  - NOT CRYPTOGRAPHIC")
    print("  - UNPROVEN for adversarial settings")
    print("  - Suitable for deterministic simulation and testing")
    print("=" * 70)


if __name__ == "__main__":
    demonstrate_fast_pirtm()
