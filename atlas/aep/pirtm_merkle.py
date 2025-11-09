"""
PIRTM Merkle tree implementation for prime binding commitments.

Provides Merkle tree construction, proof generation, and verification
for committing to prime→(class, coord) bindings.
"""
from __future__ import annotations

import json
import hashlib
from typing import List, Dict, Any


def _b2h(b: bytes) -> str:
    """BLAKE2b hash to hex string (32-byte digest)."""
    return hashlib.blake2b(b, digest_size=32).hexdigest()


def _canon(x: Any) -> bytes:
    """Canonical JSON encoding for deterministic hashing."""
    return json.dumps(x, sort_keys=True, separators=(",", ":")).encode()


def leaf_hash(item: Dict[str, Any]) -> str:
    """
    Compute leaf hash for a Merkle tree item.
    
    Args:
        item: Dictionary representing a leaf node
        
    Returns:
        BLAKE2b hex digest of canonical JSON encoding
    """
    return _b2h(_canon(item))


def _pair_hash(h1: str, h2: str) -> str:
    """
    Compute hash of two concatenated hashes.
    
    Args:
        h1: First hex hash string
        h2: Second hex hash string
        
    Returns:
        BLAKE2b hex digest of concatenated bytes
    """
    return _b2h(bytes.fromhex(h1) + bytes.fromhex(h2))


def merkle_root(items: List[Dict[str, Any]]) -> str:
    """
    Compute Merkle root of a list of items.
    
    Builds a binary Merkle tree bottom-up. If the list has odd length at any level,
    the last element is duplicated.
    
    Args:
        items: List of dictionaries to commit to
        
    Returns:
        Merkle root hash as hex string. Returns hash of null byte if items is empty.
    """
    if not items:
        return _b2h(b"\x00")
    
    level = [leaf_hash(x) for x in items]
    while len(level) > 1:
        nxt = []
        it = iter(level)
        for a in it:
            try:
                b = next(it)
            except StopIteration:
                b = a  # duplicate last
            nxt.append(_pair_hash(a, b))
        level = nxt
    return level[0]


def merkle_proof(items: List[Dict[str, Any]], index: int) -> List[str]:
    """
    Generate Merkle proof for an item at a given index.
    
    Returns the sibling hashes needed to reconstruct the path from leaf to root.
    
    Args:
        items: List of all items in the Merkle tree
        index: Index of the item to prove (0-based)
        
    Returns:
        List of sibling hashes from leaf to root
        
    Raises:
        AssertionError: If index is out of range
    """
    assert 0 <= index < len(items)
    level = [leaf_hash(x) for x in items]
    idx = index
    proof: List[str] = []
    
    while len(level) > 1:
        # sibling index
        sib = idx ^ 1
        if sib >= len(level):
            sib = idx  # duplicate case
        proof.append(level[sib])
        # move up
        idx //= 2
        nxt = []
        it = iter(level)
        for a in it:
            try:
                b = next(it)
            except StopIteration:
                b = a
            nxt.append(_b2h(bytes.fromhex(a) + bytes.fromhex(b)))
        level = nxt
    
    return proof


def merkle_verify(root: str, item: Dict[str, Any], index: int, proof: List[str]) -> bool:
    """
    Verify a Merkle proof for an item.
    
    Args:
        root: Expected Merkle root hash
        item: Item to verify
        index: Index of item in the tree
        proof: List of sibling hashes from merkle_proof
        
    Returns:
        True if proof is valid, False otherwise
    """
    h = leaf_hash(item)
    idx = index
    for sib in proof:
        if idx % 2 == 0:
            h = _b2h(bytes.fromhex(h) + bytes.fromhex(sib))
        else:
            h = _b2h(bytes.fromhex(sib) + bytes.fromhex(h))
        idx //= 2
    return h == root
