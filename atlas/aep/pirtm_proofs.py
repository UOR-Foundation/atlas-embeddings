"""
PIRTM stateless proof manager.
Side-effect-free. No storage. Deterministic IDs.
UNPROVEN: Not a cryptographic proof system.
"""
from __future__ import annotations

import json
import hashlib
from dataclasses import dataclass
from typing import Any, Dict


def _b2h(b: bytes) -> str:
    """BLAKE2b hash to hex string (32-byte digest)."""
    return hashlib.blake2b(b, digest_size=32).hexdigest()


def _canon(obj: Any) -> bytes:
    """Canonical JSON encoding for deterministic hashing."""
    return json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()


@dataclass(frozen=True)
class Proof:
    """Immutable proof record with deterministic ID."""
    proof_id: str
    kind: str
    payload_hash: str


class StatelessProofManager:
    """Stateless proof manager - no storage, deterministic IDs."""
    
    @staticmethod
    def generate(kind: str, payload: Dict[str, Any]) -> Proof:
        """
        Generate a proof from kind and payload.
        
        The proof_id is deterministically derived from (kind, payload_hash).
        No storage or side effects.
        
        Args:
            kind: Type of proof (e.g., "pirtm_update")
            payload: Dictionary containing proof data
            
        Returns:
            Proof with deterministic proof_id, kind, and payload_hash
        """
        ph = _b2h(_canon(payload))
        pid = _b2h(_canon({"k": kind, "h": ph}))
        return Proof(proof_id=pid, kind=kind, payload_hash=ph)

    @staticmethod
    def verify(proof: Proof, payload: Dict[str, Any]) -> bool:
        """
        Verify that a proof matches the given payload.
        
        Recomputes hashes from payload and checks consistency with proof.
        
        Args:
            proof: Proof to verify
            payload: Original payload data
            
        Returns:
            True if proof is valid for the payload, False otherwise
        """
        ph = _b2h(_canon(payload))
        expect_pid = _b2h(_canon({"k": proof.kind, "h": ph}))
        return (proof.payload_hash == ph) and (proof.proof_id == expect_pid)
