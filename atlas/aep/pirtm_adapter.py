"""
PIRTM adapter for stateless proof-based updates.

Provides:
- Prime binding to (class∈96, coord∈12288) via deterministic BLAKE2b mapping
- Derivation of scalar k ∈ [0,1−ε] from primes and Λ_m
- Update function T_next = F + k T
- Reverse update function
- Stateless proof generation

Side-effect-free. No storage.
"""
from __future__ import annotations

import hashlib
import json
import sys
from typing import Any, Dict, Iterable, Optional, Tuple

# Ensure we import real numpy, not the stub
# Remove current directory from path temporarily
_saved_path = sys.path[:]
_repo_indices = [i for i, p in enumerate(sys.path) if p.endswith('atlas-hologram') or p.endswith('atlas/aep') or 'atlas-hologram' in p]
for idx in reversed(_repo_indices):
    sys.path.pop(idx)

import numpy as np_real

# Restore path
sys.path = _saved_path

try:
    from .pirtm_proofs import StatelessProofManager, Proof, _b2h, _canon
except ImportError:
    from pirtm_proofs import StatelessProofManager, Proof, _b2h, _canon

# Alias for type annotations
np = np_real


# ============ Constants ============

NUM_CLASSES = 96
NUM_COORDS = 12288


# ============ Prime bindings ============


def bind_primes(primes: Iterable[int]) -> list[tuple[int, int, int]]:
    """
    Bind each prime to (prime, class∈96, coord∈12288) deterministically.
    
    Uses BLAKE2b(prime_bytes) to derive class and coord indices.
    
    Args:
        primes: Iterable of prime numbers
        
    Returns:
        List of (prime, class_idx, coord_idx) tuples
    """
    bindings = []
    for p in primes:
        p_bytes = str(p).encode()
        h = hashlib.blake2b(p_bytes, digest_size=16).digest()
        # Use first 8 bytes for class, second 8 bytes for coord
        class_idx = int.from_bytes(h[:8], 'little') % NUM_CLASSES
        coord_idx = int.from_bytes(h[8:16], 'little') % NUM_COORDS
        bindings.append((p, class_idx, coord_idx))
    return bindings


# ============ Derive k from primes ============


def derive_k(primes: Iterable[int], 
             Lambda_m: int,
             alpha: float,
             *,
             eps: float = 1e-3) -> Tuple[float, Dict[str, Any]]:
    """
    Derive scalar k ∈ [0,1−ε] from primes, Lambda_m, and alpha.
    
    The derivation uses a deterministic hash-based approach:
    1. Hash the sorted primes and Lambda_m
    2. Normalize to [0,1] 
    3. Apply alpha clipping
    4. Ensure k < 1 - eps for contractivity
    
    Args:
        primes: Iterable of primes
        Lambda_m: Modulus parameter
        alpha: Learning rate / clipping factor in [0,1]
        eps: Safety margin, k will be in [0, 1-eps]
        
    Returns:
        Tuple of (k, info_dict) where:
        - k: scalar in [0, 1-eps]
        - info_dict: diagnostic information about derivation
    """
    primes_list = sorted(list(primes))
    
    # Deterministic hash of (primes, Lambda_m)
    data = {"primes": primes_list, "Lambda_m": Lambda_m}
    h = _b2h(_canon(data))
    
    # Convert first 8 bytes to float in [0,1]
    h_int = int(h[:16], 16)  # First 8 bytes as hex = 16 hex chars
    u = (h_int % (2**53)) / (2**53)  # Use 53 bits for float precision
    
    # Apply alpha clipping
    k_raw = u * alpha
    
    # Clip to [0, 1-eps] for safety
    k = max(0.0, min(k_raw, 1.0 - eps))
    
    info = {
        "primes": primes_list,
        "Lambda_m": Lambda_m,
        "alpha": alpha,
        "u_hash": h,
        "u_float": u,
        "alpha_clipped": alpha,
        "k_raw": k_raw,
        "k": k,
        "eps": eps,
        "clipped": not (0.0 <= k_raw < 1.0 - eps),
    }
    return float(k), info


# ============ Update and reverse ============


def apply_update(T: np_real.ndarray, F: np_real.ndarray, k: float) -> np_real.ndarray:
    """
    Apply PIRTM update: T_next = F + k T
    
    Args:
        T: Current state array
        F: Force/target array
        k: Update scalar in [0,1)
        
    Returns:
        Updated state T_next
    """
    return F + k * T


def reverse_update(T_next: np_real.ndarray, F: np_real.ndarray, k: float) -> np_real.ndarray:
    """
    Invert T_next = F + k T for k in [0,1).
    
    Solves for T given T_next, F, and k.
    
    Args:
        T_next: Updated state
        F: Force/target array
        k: Update scalar used
        
    Returns:
        Original T
        
    Raises:
        ValueError: If k is not in [0,1)
    """
    if not (0.0 <= k < 1.0):
        raise ValueError("k must be in [0,1)")
    return (T_next - F) / (k + 1e-30)


# ============ Array digest ============


def _array_digest(arr: np_real.ndarray) -> str:
    """
    Compute deterministic digest of numpy array.
    
    Args:
        arr: Numpy array
        
    Returns:
        BLAKE2b hex digest of array data
    """
    # Ensure C-contiguous for deterministic bytes
    arr_c = np.ascontiguousarray(arr)
    return _b2h(arr_c.tobytes())


# ============ Adapter API ============


def pirtm_update(T: np_real.ndarray,
                 F: np_real.ndarray,
                 primes: Iterable[int],
                 Lambda_m: int,
                 alpha: float,
                 *,
                 eps: float = 1e-3,
                 actor_id: str = "",
                 context: Optional[Dict[str, Any]] = None) -> Tuple[np_real.ndarray, Proof, Dict[str, Any]]:
    """
    Perform one PIRTM update with runtime |k|<1 enforcement and stateless proof.

    The update computes T_next = F + k T where k is deterministically derived
    from the primes, Lambda_m, and alpha. A stateless proof is generated that
    can be verified by recomputing the payload hash.

    Args:
        T: Current state array
        F: Force/target array (must match T.shape)
        primes: Iterable of prime numbers for binding
        Lambda_m: Modulus parameter
        alpha: Learning rate in [0,1]
        eps: Safety margin, k < 1-eps (default 1e-3)
        actor_id: Optional identifier for the actor performing the update
        context: Optional context dictionary for proof payload
        
    Returns:
        Tuple of (T_next, proof, info) where:
        - T_next: Updated state array
        - proof: Stateless Proof object
        - info: Dictionary with k, k_info, bindings preview, and digest
        
    Raises:
        ValueError: If T and F shapes don't match
        
    Side-effect-free: does not write to any ledger or global store.
    """
    if T.shape != F.shape:
        raise ValueError("T and F must have the same shape")

    k, k_info = derive_k(primes, Lambda_m, alpha, eps=eps)
    T_next = apply_update(T, F, k)

    # Prime bindings summary digest
    bindings = bind_primes(primes)
    bind_digest = _b2h(_canon(bindings))

    payload = {
        "kind": "pirtm_update",
        "actor_id": actor_id,
        "context": context or {},
        "T_digest": _array_digest(np.asarray(T)),
        "F_digest": _array_digest(np.asarray(F)),
        "shape": list(T.shape),
        "k": k,
        "k_info": k_info,
        "bindings_digest": bind_digest,
        "Lambda_m": int(Lambda_m),
    }

    proof = StatelessProofManager.generate("pirtm_update", payload)

    info = {
        "k": k,
        "k_info": k_info,
        "bindings": bindings[:32],  # first 32 for quick inspection
        "bindings_digest": bind_digest,
    }

    return T_next, proof, info
