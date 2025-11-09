"""
PIRTM Adapter (vectorized rates) — FAST K-GEN

Same API as pirtm_adapter_vec.pirtm_update_vec but uses PRNG-based
k generation with GPU support via CuPy when available.
"""
from __future__ import annotations

from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple
import sys

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
    from .pirtm_merkle import merkle_root
    from .pirtm_adapter import bind_primes
    from .pirtm_kgen import k_vector
except ImportError:
    from pirtm_proofs import StatelessProofManager, Proof, _b2h, _canon
    from pirtm_merkle import merkle_root
    from pirtm_adapter import bind_primes
    from pirtm_kgen import k_vector

# Alias for type annotations
np = np_real

Address = Tuple[int, int]


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


def _default_addresses(n: int) -> List[Address]:
    """
    Generate default deterministic address mapping.
    
    Args:
        n: Number of addresses to generate
        
    Returns:
        List of (class, coord) tuples
    """
    addrs: List[Address] = []
    for j in range(n):
        c = j % 96
        i = (j // 96) % 12288
        addrs.append((c, i))
    return addrs


def pirtm_update_vec(T: np_real.ndarray,
                     F: np_real.ndarray,
                     primes: Iterable[int],
                     Lambda_m: int,
                     alpha: float,
                     *,
                     eps: float = 1e-3,
                     addresses: Optional[Sequence[Address]] = None,
                     backend: str | None = None,
                     actor_id: str = "",
                     context: Optional[Dict[str, Any]] = None) -> Tuple[np_real.ndarray, np_real.ndarray, Proof, Dict[str, Any]]:
    """
    Perform vectorized PIRTM update with fast PRNG-based k generation.
    
    Uses PRNG-based k_vector generation for high performance. Supports
    GPU acceleration via CuPy when backend="cupy".
    
    Args:
        T: Current state array (any shape)
        F: Force/target array (must match T.shape)
        primes: Iterable of prime numbers for binding
        Lambda_m: Modulus parameter
        alpha: Learning rate in [0,1]
        eps: Safety margin, k_i < 1-eps (default 1e-3)
        addresses: Optional address mapping. If None, uses default.
        backend: "numpy" or "cupy". If "cupy", uses GPU if available.
        actor_id: Optional identifier for the actor
        context: Optional context dictionary for proof payload
        
    Returns:
        Tuple of (T_next, k_vec, proof, info) where:
        - T_next: Updated state array (same shape as T)
        - k_vec: Per-coordinate k values (flattened, NumPy array)
        - proof: Stateless Proof object
        - info: Dictionary with k_stats, bindings info, seed_hex, backend
        
    Raises:
        ValueError: If T and F shapes don't match
    """
    if T.shape != F.shape:
        raise ValueError("T and F must have the same shape")
    
    T_flat = T.reshape(-1)
    F_flat = F.reshape(-1)
    
    addrs = list(addresses) if addresses is not None else _default_addresses(T_flat.size)
    k_vec, k_meta = k_vector(T_flat.size, primes, Lambda_m, alpha, eps=eps, addresses=addrs, backend=backend)
    
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
        "addresses_digest": k_meta["addresses_digest"],
        "primes_digest": _b2h(_canon([int(p) for p in primes])),
        "Lambda_m": int(Lambda_m),
        "eps": float(eps),
        "seed_hex": k_meta["seed_hex"],
        "merkle_root": mr,
    }
    
    proof = StatelessProofManager.generate("pirtm_update_vec", payload)
    
    info = {
        "k_stats": payload["k_stats"],
        "k_first": k_vec[:8].tolist(),
        "bindings_root": mr,
        "bindings_preview": leaves[:8],
        "addresses_preview": addrs[:8],
        "seed_hex": k_meta["seed_hex"],
        "backend": backend or "numpy",
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
