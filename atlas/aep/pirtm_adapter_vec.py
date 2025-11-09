"""
PIRTM vectorized adapter for per-coordinate updates.

Provides:
- Vectorized k derivation: k_i ∈ [0,1−ε] for each coordinate
- Deterministic address mapping: index → (class∈96, coord∈12288)
- Vectorized update: T_next = F + k_vec ⊙ T (element-wise)
- Reversible operations with per-coordinate rates
- Merkle commitments for prime bindings
"""
from __future__ import annotations

import hashlib
import json
import sys
from typing import Any, Dict, Iterable, List, Optional, Tuple

# Ensure we import real numpy, not the stub
_saved_path = sys.path[:]
_repo_indices = [i for i, p in enumerate(sys.path) if p.endswith('atlas-hologram') or p.endswith('atlas/aep') or 'atlas-hologram' in p]
for idx in reversed(_repo_indices):
    sys.path.pop(idx)

import numpy as np_real

# Restore path
sys.path = _saved_path

try:
    from .pirtm_proofs import StatelessProofManager, Proof, _b2h, _canon
    from .pirtm_merkle import merkle_root, leaf_hash
    from .pirtm_adapter import bind_primes, NUM_CLASSES, NUM_COORDS
except ImportError:
    from pirtm_proofs import StatelessProofManager, Proof, _b2h, _canon
    from pirtm_merkle import merkle_root, leaf_hash
    from pirtm_adapter import bind_primes, NUM_CLASSES, NUM_COORDS

# Alias for type annotations
np = np_real


# ============ Address mapping ============


def default_address_map(size: int) -> List[Tuple[int, int]]:
    """
    Generate default deterministic address mapping for flat indices.
    
    Maps each flat index i to (class_idx, coord_idx) using modulo arithmetic
    over the 96 × 12288 address space.
    
    Args:
        size: Number of addresses to generate
        
    Returns:
        List of (class_idx, coord_idx) tuples
    """
    addresses = []
    for i in range(size):
        class_idx = i % NUM_CLASSES
        coord_idx = (i // NUM_CLASSES) % NUM_COORDS
        addresses.append((class_idx, coord_idx))
    return addresses


# ============ Vectorized k derivation ============


def derive_k_vector(primes: Iterable[int],
                   Lambda_m: int,
                   alpha: float,
                   size: int,
                   *,
                   eps: float = 1e-3,
                   addresses: Optional[List[Tuple[int, int]]] = None) -> Tuple[np_real.ndarray, List[Tuple[int, int]], Dict[str, Any]]:
    """
    Derive per-coordinate k vector from primes and addresses.
    
    Each coordinate gets its own k_i ∈ [0,1−ε] derived deterministically from:
    - The list of primes
    - Lambda_m modulus
    - The coordinate's address (class, coord)
    - The coordinate's flat index i
    
    Args:
        primes: Iterable of prime numbers
        Lambda_m: Modulus parameter
        alpha: Learning rate / clipping factor in [0,1]
        size: Length of k vector to generate
        eps: Safety margin, k_i will be in [0, 1-eps]
        addresses: Optional list of (class, coord) tuples. If None, uses default mapping.
        
    Returns:
        Tuple of (k_vec, addresses, meta) where:
        - k_vec: numpy array of shape (size,) with k_i ∈ [0, 1-eps]
        - addresses: list of (class, coord) tuples used
        - meta: dict with primes_digest, Lambda_m, eps
    """
    primes_list = sorted(list(primes))
    
    # Generate or validate addresses
    if addresses is None:
        addresses = default_address_map(size)
    elif len(addresses) != size:
        raise ValueError(f"addresses length {len(addresses)} != size {size}")
    
    # Compute primes digest for metadata
    primes_digest = _b2h(_canon(primes_list))
    
    k_vec = np.zeros(size, dtype=float)
    
    for i in range(size):
        class_idx, coord_idx = addresses[i]
        
        # Deterministic hash of (primes, Lambda_m, address, index)
        data = {
            "primes": primes_list,
            "Lambda_m": Lambda_m,
            "address": [class_idx, coord_idx],
            "index": i
        }
        h = _b2h(_canon(data))
        
        # Convert first 8 bytes to float in [0,1]
        h_int = int(h[:16], 16)  # First 8 bytes as hex = 16 hex chars
        u = (h_int % (2**53)) / (2**53)  # Use 53 bits for float precision
        
        # Apply alpha clipping
        k_raw = u * alpha
        
        # Clip to [0, 1-eps] for safety
        k_i = max(0.0, min(k_raw, 1.0 - eps))
        
        k_vec[i] = k_i
    
    meta = {
        "primes_digest": primes_digest,
        "Lambda_m": Lambda_m,
        "eps": eps,
    }
    
    return k_vec, addresses, meta


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


# ============ Vectorized update API ============


def pirtm_update_vec(T: np_real.ndarray,
                     F: np_real.ndarray,
                     primes: Iterable[int],
                     Lambda_m: int,
                     alpha: float,
                     *,
                     eps: float = 1e-3,
                     addresses: Optional[List[Tuple[int, int]]] = None,
                     actor_id: str = "",
                     context: Optional[Dict[str, Any]] = None) -> Tuple[np_real.ndarray, np_real.ndarray, Proof, Dict[str, Any]]:
    """
    Perform vectorized PIRTM update with per-coordinate k values.
    
    Computes T_next = F + k_vec ⊙ T where each k_i is derived independently
    from the coordinate's address and index.
    
    Args:
        T: Current state array (any shape)
        F: Force/target array (must match T.shape)
        primes: Iterable of prime numbers for binding
        Lambda_m: Modulus parameter
        alpha: Learning rate in [0,1]
        eps: Safety margin, k_i < 1-eps (default 1e-3)
        addresses: Optional address mapping. If None, uses default.
        actor_id: Optional identifier for the actor
        context: Optional context dictionary for proof payload
        
    Returns:
        Tuple of (T_next, k_vec, proof, info) where:
        - T_next: Updated state array (same shape as T)
        - k_vec: Per-coordinate k values (flattened)
        - proof: Stateless Proof object
        - info: Dictionary with k_stats, bindings info, addresses preview
        
    Raises:
        ValueError: If T and F shapes don't match
    """
    if T.shape != F.shape:
        raise ValueError("T and F must have the same shape")
    
    T_flat = T.reshape(-1)
    F_flat = F.reshape(-1)
    
    k_vec, addrs, meta = derive_k_vector(primes, Lambda_m, alpha, T_flat.size, eps=eps, addresses=addresses)
    
    Tn_flat = F_flat + k_vec * T_flat
    T_next = Tn_flat.reshape(T.shape)
    
    # Merkle root for prime bindings
    bindings = bind_primes(primes)
    leaves = [{"p": p, "class": c, "coord": i} for (p, c, i) in bindings]
    mr = merkle_root(leaves)
    
    payload = {
        "kind": "pirtm_update_vec",
        "actor_id": actor_id,
        "context": context or {},
        "T_digest": _array_digest(np.asarray(T)),
        "F_digest": _array_digest(np.asarray(F)),
        "shape": list(T.shape),
        "k_digest": _b2h(k_vec.tobytes()),
        "k_stats": {
            "min": float(k_vec.min()),
            "max": float(k_vec.max()),
            "mean": float(k_vec.mean()),
        },
        "addresses_digest": _b2h(_canon(addrs[:256])),
        "primes_digest": meta["primes_digest"],
        "Lambda_m": meta["Lambda_m"],
        "eps": meta["eps"],
        "merkle_root": mr,
    }
    
    proof = StatelessProofManager.generate("pirtm_update_vec", payload)
    
    info = {
        "k_stats": payload["k_stats"],
        "k_first": k_vec[:8].tolist(),
        "bindings_root": mr,
        "bindings_preview": leaves[:8],
        "addresses_preview": addrs[:8],
    }
    
    return T_next, k_vec, proof, info


def reverse_update_vec(T_next: np_real.ndarray, F: np_real.ndarray, k_vec: np_real.ndarray) -> np_real.ndarray:
    """
    Invert vectorized PIRTM update.
    
    Solves T from T_next = F + k_vec ⊙ T element-wise.
    
    Args:
        T_next: Updated state array
        F: Force/target array
        k_vec: Per-coordinate k values
        
    Returns:
        Original T array (same shape as T_next)
        
    Raises:
        ValueError: If shapes don't match
    """
    if T_next.shape != F.shape:
        raise ValueError("shape mismatch")
    if k_vec.size != T_next.size:
        raise ValueError("k_vec size mismatch")
    
    T_flat = (T_next.reshape(-1) - F.reshape(-1)) / (k_vec.reshape(-1) + 1e-30)
    return T_flat.reshape(T_next.shape)
