"""
Fast k-vector generator for PIRTM.

Deterministic PRNG keyed by (primes, Lambda_m, addresses_digest).
Supports NumPy CPU and CuPy GPU backends. Preserves invariants:
  - k_i ∈ [0, 1−eps]
  - Deterministic for the same inputs and address order

NOT CRYPTOGRAPHIC. UNPROVEN for adversarial settings.
"""
from __future__ import annotations

from typing import Iterable, Sequence, Tuple, Dict, Any, Optional
import sys
from pathlib import Path

# Ensure we import real numpy, not the stub
_saved_path = sys.path[:]
_repo_indices = [i for i, p in enumerate(sys.path) if p.endswith('atlas-hologram') or p.endswith('atlas/aep') or 'atlas-hologram' in p]
for idx in reversed(_repo_indices):
    sys.path.pop(idx)

import numpy as np_real

# Restore path
sys.path = _saved_path

try:
    import cupy as cp  # optional
except Exception:  # pragma: no cover
    cp = None  # type: ignore

try:
    from .pirtm_proofs import _b2h, _canon
except ImportError:
    from pirtm_proofs import _b2h, _canon

# Alias for type annotations
np = np_real

Address = Tuple[int, int]


def _addresses_digest(addrs: Sequence[Address]) -> str:
    """
    Compute deterministic digest of address sequence.
    
    Truncates to first 4096 addresses for digest to avoid huge JSON;
    still deterministic for given order.
    
    Args:
        addrs: Sequence of (class, coord) tuples
        
    Returns:
        Hex digest string of truncated address list
    """
    # Truncate to first 4096 addresses for digest
    truncated = [(int(c), int(i)) for (c, i) in addrs[:4096]]
    return _b2h(_canon(truncated))


def _seed_material(primes: Iterable[int], Lambda_m: int, addrs: Sequence[Address]) -> Dict[str, Any]:
    """
    Generate seed material from primes, Lambda_m, and addresses.
    
    Creates a deterministic seed by hashing the canonical representation
    of the input parameters.
    
    Args:
        primes: Iterable of prime numbers
        Lambda_m: Modulus parameter
        addrs: Sequence of (class, coord) addresses
        
    Returns:
        Dictionary with seed_hex and addresses_digest
    """
    p_list = [int(p) for p in primes]
    ad = _addresses_digest(addrs)
    mat = {"primes": p_list, "Lambda_m": int(Lambda_m), "addr_digest": ad}
    seed_hex = _b2h(_canon(mat))
    return {"seed_hex": seed_hex, "addresses_digest": ad}


def _seed_numpy(seed_hex: str):
    """
    Create NumPy random generator from hex seed.
    
    Converts 256-bit hex seed into SeedSequence entropy for PCG64 generator.
    
    Args:
        seed_hex: Hex string seed (64 characters = 32 bytes)
        
    Returns:
        NumPy Generator with PCG64 bit generator
    """
    # Convert 256-bit hex into SeedSequence entropy
    b = bytes.fromhex(seed_hex)
    u32 = np.frombuffer(b, dtype=np.uint32)
    ss = np.random.SeedSequence(u32)
    return np.random.Generator(np.random.PCG64(ss))


def _seed_cupy(seed_hex: str):
    """
    Create CuPy random state from hex seed.
    
    Uses first 64 bits as seed for CuPy RandomState.
    
    Args:
        seed_hex: Hex string seed
        
    Returns:
        CuPy RandomState or None if CuPy not available
    """
    if cp is None:
        return None
    # Use first 64 bits as seed
    seed64 = int(seed_hex[:16], 16) & 0xFFFFFFFFFFFFFFFF
    rs = cp.random.RandomState(seed64)
    return rs


def k_vector(size: int,
             primes: Iterable[int],
             Lambda_m: int,
             alpha: float,
             *,
             eps: float = 1e-3,
             addresses: Optional[Sequence[Address]] = None,
             backend: str | None = None) -> Tuple[np_real.ndarray, Dict[str, Any]]:
    """
    Return k_vec in [0,1−eps] with fast vectorized generation.
    
    Uses PRNG-based generation for high performance. Deterministic
    given the same inputs and address order.
    
    Args:
        size: Length of k vector to generate
        primes: Iterable of prime numbers
        Lambda_m: Modulus parameter
        alpha: Learning rate / clipping factor in [0,1]
        eps: Safety margin, k_i < 1-eps (default 1e-3)
        addresses: Optional sequence of (class, coord) tuples. If None, uses default.
        backend: "numpy" or "cupy". If "cupy" and CuPy available, uses GPU.
        
    Returns:
        Tuple of (k_vec, info) where:
        - k_vec: NumPy array of shape (size,) with k_i ∈ [0, 1-eps]
        - info: Dictionary with metadata about generation
        
    Note:
        If backend == "cupy" and CuPy is available, returns a NumPy array
        produced from GPU values for compatibility.
    """
    rate = max(0.0, min(float(alpha), 1.0 - eps))
    
    # Generate or use provided addresses
    if addresses is not None:
        addrs = list(addresses)
    else:
        addrs = [(i % 96, (i // 96) % 12288) for i in range(size)]
    
    mat = _seed_material(primes, Lambda_m, addrs)
    
    use_gpu = (backend or "").lower() == "cupy" and (cp is not None)
    
    if use_gpu:
        rs = _seed_cupy(mat["seed_hex"])  # type: ignore
        u = rs.random(size)  # type: ignore
        # move to host for compatibility
        k = np.minimum(rate * u.get(), 1.0 - eps)
    else:
        rg = _seed_numpy(mat["seed_hex"])  # NumPy Generator
        u = rg.random(size)
        k = np.minimum(rate * u, 1.0 - eps)
    
    info = {
        "alpha_clipped": rate,
        "addresses_digest": mat["addresses_digest"],
        "seed_hex": mat["seed_hex"],
        "eps": eps,
    }
    return k.astype(float), info
