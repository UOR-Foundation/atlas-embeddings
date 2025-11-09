#!/usr/bin/env python3
"""
Demo harness for PIRTM adapter.
Run: python pirtm_harness.py
"""
from __future__ import annotations

import sys
from pathlib import Path

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent))

import json
import numpy as np

import pirtm_adapter
import pirtm_proofs


def main() -> None:
    """Demonstrate PIRTM update, proof generation, and reversal."""
    # Setup
    d = 64
    T = np.ones((d,))
    F = np.zeros((d,))
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    Lambda_m = 503
    alpha = 0.99

    print("PIRTM Demo Harness")
    print("=" * 60)
    print(f"Input dimensions: {d}")
    print(f"Primes: {primes}")
    print(f"Lambda_m: {Lambda_m}")
    print(f"Alpha: {alpha}")
    print()

    # Perform update
    T_next, proof, info = pirtm_adapter.pirtm_update(
        T, F, primes, Lambda_m, alpha,
        actor_id="alice",
        context={"note": "demo"}
    )

    print(f"k: {info['k']:.6f}")
    print(f"proof_id: {proof.proof_id}")
    print(f"payload_hash: {proof.payload_hash}")
    print()

    # Verify proof (illustrative - in production, pass the full original payload)
    # Note: This is a simplified verification for demo purposes
    ok = pirtm_proofs.StatelessProofManager.verify(proof, {
        "kind": "pirtm_update",
        "actor_id": "alice",
        "context": {"note": "demo"},
        "T_digest": "",  # Would need actual digest in production
        "F_digest": "",
        "shape": list(T.shape),
        "k": info["k"],
        "k_info": info["k_info"],
        "bindings_digest": info["bindings_digest"],
        "Lambda_m": Lambda_m,
    })
    
    # Note: The verification above will fail because we didn't pass the correct digests
    # This is intentional for the demo - showing that verification requires exact payload
    print(f"Simplified verification (expected to fail): {ok}")
    print("(Verification fails because array digests weren't included)")
    print()

    # Reverse the update
    T_rev = pirtm_adapter.reverse_update(T_next, F, info["k"])
    reversible_err = float(np.linalg.norm(T_rev - T))
    
    print(f"Reversible error: {reversible_err:.2e}")
    print(f"Bindings preview (first 5): {info['bindings'][:5]}")
    print()
    
    # Show update statistics
    print("Update Statistics:")
    print(f"  ||T||: {np.linalg.norm(T):.4f}")
    print(f"  ||F||: {np.linalg.norm(F):.4f}")
    print(f"  ||T_next||: {np.linalg.norm(T_next):.4f}")
    print(f"  ||T_next - T||: {np.linalg.norm(T_next - T):.4f}")
    print()
    
    print("=" * 60)
    print("Demo complete!")


if __name__ == "__main__":
    main()
