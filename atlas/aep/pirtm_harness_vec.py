#!/usr/bin/env python3
"""
PIRTM vectorized demo.
Run: python pirtm_harness_vec.py
"""
from __future__ import annotations

import sys
from pathlib import Path

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent))

import json
import numpy as np

from pirtm_adapter_vec import pirtm_update_vec, reverse_update_vec


def main():
    """Demonstrate vectorized PIRTM update with per-coordinate k values."""
    d = 96 * 8  # arbitrary demo length
    T = np.arange(d, dtype=float)
    F = np.zeros_like(T)
    
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    Lambda_m = 503
    alpha = 0.95
    
    print("PIRTM Vectorized Demo")
    print("=" * 60)
    print(f"Vector dimension: {d}")
    print(f"Primes: {primes}")
    print(f"Lambda_m: {Lambda_m}")
    print(f"Alpha: {alpha}")
    print()
    
    T_next, k_vec, proof, info = pirtm_update_vec(
        T, F, primes, Lambda_m, alpha,
        actor_id="atlas",
        context={"demo": True}
    )
    
    T_prev = reverse_update_vec(T_next, F, k_vec)
    
    print("k_stats:", info["k_stats"])  # min/max/mean
    print("reversible_err:", float(np.linalg.norm(T_prev - T)))
    print("proof_id:", proof.proof_id)
    print("bindings_root:", info["bindings_root"])
    print("k_first:", info["k_first"])  # preview
    print()
    
    # Show some statistics
    print("Update Statistics:")
    print(f"  ||T||: {np.linalg.norm(T):.4f}")
    print(f"  ||F||: {np.linalg.norm(F):.4f}")
    print(f"  ||T_next||: {np.linalg.norm(T_next):.4f}")
    print(f"  ||T_next - T||: {np.linalg.norm(T_next - T):.4f}")
    print()
    
    # Show address preview
    print("Addresses preview (first 8):")
    for i, (c, coord) in enumerate(info["addresses_preview"]):
        print(f"  [{i}] -> (class={c}, coord={coord})")
    print()
    
    # Show bindings preview
    print("Bindings preview (first 8):")
    for b in info["bindings_preview"]:
        print(f"  p={b['p']}, class={b['class']}, coord={b['coord']}")
    print()
    
    print("=" * 60)
    print("Demo complete!")


if __name__ == "__main__":
    main()
