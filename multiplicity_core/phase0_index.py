"""
Phase 0 — Hard Constraints: Index Map and Policies

This module implements the Phase 0 requirements:
1. Fixed index size n = 12,288 (48×256)
2. Total index map: index(page, belt, offset)
3. Projector admissibility enforcement: p^r | n
4. Prime and permutation policies (UNPROVEN)

All policies are marked UNPROVEN until mathematically fixed and verified.
"""

from __future__ import annotations
from typing import Tuple, Callable, Optional
from dataclasses import dataclass

# ============================================================================
# Phase 0 Constants
# ============================================================================

# Fixed index size: 48 pages × 256 bytes = 12,288
INDEX_SIZE = 12288
NUM_PAGES = 48
BYTES_PER_PAGE = 256

# Belt parameters (metadata vs encoded)
NUM_BELTS = 1  # Default: belt is metadata, not encoded in index


# ============================================================================
# Index Map Functions
# ============================================================================

def index_map(page: int, belt: int, offset: int, encode_belt: bool = False) -> int:
    """
    Total index map: index(page, belt, offset)
    
    Two modes:
    1. Default (encode_belt=False): index = page*256 + offset
       Belt is treated as metadata and not encoded in the address.
    
    2. Belt encoding (encode_belt=True): index = page*(256*B) + belt*256 + offset
       Where B is the number of belts. This packs belt into the address.
    
    Args:
        page: Page number in [0, NUM_PAGES-1]
        belt: Belt number (metadata or encoded depending on mode)
        offset: Byte offset in [0, BYTES_PER_PAGE-1]
        encode_belt: If True, encode belt in the address
    
    Returns:
        Linear index in [0, INDEX_SIZE-1] (default mode)
        or extended index if belt encoding is used
    
    Raises:
        ValueError: If parameters are out of range
    """
    if not (0 <= page < NUM_PAGES):
        raise ValueError(f"page must be in [0, {NUM_PAGES-1}], got {page}")
    if not (0 <= offset < BYTES_PER_PAGE):
        raise ValueError(f"offset must be in [0, {BYTES_PER_PAGE-1}], got {offset}")
    
    if encode_belt:
        # Belt encoding mode: page*(256*B) + belt*256 + offset
        if not (0 <= belt < NUM_BELTS):
            raise ValueError(f"belt must be in [0, {NUM_BELTS-1}], got {belt}")
        return page * (BYTES_PER_PAGE * NUM_BELTS) + belt * BYTES_PER_PAGE + offset
    else:
        # Default mode: belt is metadata, index = page*256 + offset
        # belt parameter is ignored in the calculation but can be stored separately
        return page * BYTES_PER_PAGE + offset


def inverse_index_map(index: int, encode_belt: bool = False) -> Tuple[int, int, int]:
    """
    Inverse index map: linear index → (page, belt, offset)
    
    Args:
        index: Linear index
        encode_belt: If True, decode belt from the address
    
    Returns:
        (page, belt, offset) triple
    
    Raises:
        ValueError: If index is out of range
    """
    if encode_belt:
        max_index = NUM_PAGES * BYTES_PER_PAGE * NUM_BELTS - 1
        if not (0 <= index <= max_index):
            raise ValueError(f"index must be in [0, {max_index}], got {index}")
        
        page = index // (BYTES_PER_PAGE * NUM_BELTS)
        remainder = index % (BYTES_PER_PAGE * NUM_BELTS)
        belt = remainder // BYTES_PER_PAGE
        offset = remainder % BYTES_PER_PAGE
        return page, belt, offset
    else:
        if not (0 <= index < INDEX_SIZE):
            raise ValueError(f"index must be in [0, {INDEX_SIZE-1}], got {index}")
        
        page = index // BYTES_PER_PAGE
        offset = index % BYTES_PER_PAGE
        belt = 0  # Default belt when not encoded
        return page, belt, offset


@dataclass
class IndexAddress:
    """Full address with page, belt, and offset components."""
    page: int
    belt: int
    offset: int
    linear_index: int
    
    def __str__(self) -> str:
        return f"IndexAddress(page={self.page}, belt={self.belt}, offset={self.offset}, index={self.linear_index})"


def make_address(page: int, belt: int, offset: int, encode_belt: bool = False) -> IndexAddress:
    """
    Create a full address from components.
    
    Args:
        page: Page number
        belt: Belt number (metadata or encoded)
        offset: Byte offset
        encode_belt: If True, encode belt in address
    
    Returns:
        IndexAddress with all components
    """
    linear_index = index_map(page, belt, offset, encode_belt)
    return IndexAddress(page=page, belt=belt, offset=offset, linear_index=linear_index)


def decode_address(index: int, encode_belt: bool = False) -> IndexAddress:
    """
    Decode linear index to full address.
    
    Args:
        index: Linear index
        encode_belt: If True, decode belt from address
    
    Returns:
        IndexAddress with all components
    """
    page, belt, offset = inverse_index_map(index, encode_belt)
    return IndexAddress(page=page, belt=belt, offset=offset, linear_index=index)


# ============================================================================
# Projector Admissibility
# ============================================================================

def prime_factors(n: int) -> dict[int, int]:
    """
    Compute prime factorization of n.
    
    Args:
        n: Positive integer
    
    Returns:
        Dictionary mapping prime → exponent
    """
    if n <= 1:
        return {}
    
    factors = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    
    return factors


def check_projector_admissibility(p: int, r: int, n: int = INDEX_SIZE) -> bool:
    """
    Check projector admissibility: p^r | n (p^r divides n)
    
    A projector with prime p and level r is admissible if p^r divides the index size n.
    
    Args:
        p: Prime number
        r: Exponent/level (positive integer)
        n: Index size (default: INDEX_SIZE = 12,288)
    
    Returns:
        True if p^r divides n, False otherwise
    """
    if p <= 1 or r <= 0:
        return False
    
    # Check if p^r divides n
    return n % (p ** r) == 0


def max_admissible_level(p: int, n: int = INDEX_SIZE) -> int:
    """
    Find maximum admissible level r for prime p.
    
    Returns the largest r such that p^r divides n.
    
    Args:
        p: Prime number
        n: Index size (default: INDEX_SIZE = 12,288)
    
    Returns:
        Maximum level r, or 0 if p does not divide n
    """
    factors = prime_factors(n)
    return factors.get(p, 0)


def list_admissible_projectors(n: int = INDEX_SIZE, max_prime: int = 100) -> list[Tuple[int, int]]:
    """
    List all admissible (p, r) pairs for the given index size.
    
    Args:
        n: Index size (default: INDEX_SIZE = 12,288)
        max_prime: Maximum prime to consider
    
    Returns:
        List of (p, r) pairs where p^r | n
    """
    factors = prime_factors(n)
    admissible = []
    
    for p, max_r in factors.items():
        if p <= max_prime:
            for r in range(1, max_r + 1):
                admissible.append((p, r))
    
    return sorted(admissible)


# ============================================================================
# Policy Functions (UNPROVEN)
# ============================================================================

# WARNING: All policies below are marked UNPROVEN.
# These are placeholder implementations until mathematical verification is complete.

def prime_policy_default(d: int) -> int:
    """
    UNPROVEN: Default prime policy.
    
    Maps modality d to prime p.
    Default: p = 3 for all d, unless class metadata forces another prime.
    
    Args:
        d: Modality index (typically 0, 1, or 2 for neutral, produce, consume)
    
    Returns:
        Prime number p
    
    Note:
        This is a placeholder. Mark as UNPROVEN until fixed.
    """
    # Default to p=3 for all modalities
    return 3


def level_policy_default(d: int) -> int:
    """
    UNPROVEN: Default level policy.
    
    Maps modality d to level r.
    
    Args:
        d: Modality index
    
    Returns:
        Level r (positive integer)
    
    Note:
        This is a placeholder. Mark as UNPROVEN until fixed.
    """
    # Default to r=1 for all modalities
    return 1


def perm_policy_default(d: int) -> list[int]:
    """
    UNPROVEN: Default permutation policy.
    
    Maps modality d to permutation π.
    
    Args:
        d: Modality index
    
    Returns:
        Permutation as a list (identity permutation as placeholder)
    
    Note:
        This is a placeholder. Mark as UNPROVEN until fixed.
    """
    # Default to identity permutation
    # For now, return empty list to indicate identity
    return []


# Policy type definitions
PrimePolicy = Callable[[int], int]
LevelPolicy = Callable[[int], int]
PermPolicy = Callable[[int], list[int]]


@dataclass
class PolicySet:
    """
    Container for all Phase 0 policies.
    
    All policies are UNPROVEN until mathematically verified.
    """
    prime_policy: PrimePolicy
    level_policy: LevelPolicy
    perm_policy: PermPolicy
    status: str = "UNPROVEN"  # Status: UNPROVEN, VERIFIED, etc.
    
    def __post_init__(self):
        """Warn if policies are not marked as proven."""
        if self.status != "VERIFIED":
            import warnings
            warnings.warn(
                f"PolicySet status is {self.status}. "
                "These policies are not mathematically verified.",
                UserWarning
            )


# Default policy set (UNPROVEN)
DEFAULT_POLICIES = PolicySet(
    prime_policy=prime_policy_default,
    level_policy=level_policy_default,
    perm_policy=perm_policy_default,
    status="UNPROVEN"
)


# ============================================================================
# Validation and Diagnostics
# ============================================================================

def validate_phase0_constraints() -> dict:
    """
    Validate Phase 0 hard constraints.
    
    Returns:
        Dictionary with validation results
    """
    results = {
        "index_size": INDEX_SIZE,
        "index_size_check": INDEX_SIZE == 12288,
        "pages": NUM_PAGES,
        "bytes_per_page": BYTES_PER_PAGE,
        "factorization": prime_factors(INDEX_SIZE),
        "admissible_projectors": list_admissible_projectors(INDEX_SIZE, max_prime=20),
        "policies_status": DEFAULT_POLICIES.status
    }
    
    # Check that INDEX_SIZE = NUM_PAGES * BYTES_PER_PAGE
    results["size_consistency"] = (INDEX_SIZE == NUM_PAGES * BYTES_PER_PAGE)
    
    return results


def print_phase0_summary():
    """Print Phase 0 configuration summary."""
    print("=" * 70)
    print("Phase 0 — Hard Constraints Summary")
    print("=" * 70)
    print(f"Index size n = {INDEX_SIZE:,} (fixed)")
    print(f"Pages: {NUM_PAGES}")
    print(f"Bytes per page: {BYTES_PER_PAGE}")
    print(f"Formula: {NUM_PAGES} × {BYTES_PER_PAGE} = {INDEX_SIZE:,}")
    print()
    
    factors = prime_factors(INDEX_SIZE)
    print(f"Prime factorization: {INDEX_SIZE} = ", end="")
    factor_str = " × ".join(f"{p}^{e}" for p, e in sorted(factors.items()))
    print(factor_str)
    print()
    
    print("Admissible projectors (p^r | n, p ≤ 20):")
    for p, r in list_admissible_projectors(INDEX_SIZE, max_prime=20):
        print(f"  (p={p}, r={r}): {p}^{r} = {p**r}")
    print()
    
    print("Policies (status: UNPROVEN):")
    print(f"  primePolicy(d) → p (default: p=3)")
    print(f"  levelPolicy(d) → r (default: r=1)")
    print(f"  permPolicy(d) → π (default: identity)")
    print()
    print("⚠️  All policies are UNPROVEN until mathematically fixed and verified.")
    print("=" * 70)


__all__ = [
    # Constants
    "INDEX_SIZE",
    "NUM_PAGES",
    "BYTES_PER_PAGE",
    "NUM_BELTS",
    
    # Index map
    "index_map",
    "inverse_index_map",
    "IndexAddress",
    "make_address",
    "decode_address",
    
    # Projector admissibility
    "prime_factors",
    "check_projector_admissibility",
    "max_admissible_level",
    "list_admissible_projectors",
    
    # Policies (UNPROVEN)
    "prime_policy_default",
    "level_policy_default",
    "perm_policy_default",
    "PrimePolicy",
    "LevelPolicy",
    "PermPolicy",
    "PolicySet",
    "DEFAULT_POLICIES",
    
    # Validation
    "validate_phase0_constraints",
    "print_phase0_summary",
]
