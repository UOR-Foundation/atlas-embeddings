"""
Atlas ⨯ MTPI — Local Identity/ZK Layer (stub)

Generates deterministic local-hash proofs and verifies them in-node.
Only submit on-chain when lawful. Replace submit_on_chain with your publisher.
UNPROVEN: This is a placeholder, not a cryptographic proof system.
"""
from __future__ import annotations

import json
import time
import hashlib
from dataclasses import dataclass
from typing import Any, Dict, List


def _now_epoch_ms() -> int:
    return int(time.time() * 1000)


def _blake2b_hex(data: bytes) -> str:
    return hashlib.blake2b(data, digest_size=32).hexdigest()


@dataclass
class Proof:
    proof_id: str
    kind: str  # "ethics_commutation" | "sovereignty_gate"
    payload_hash: str
    created_ms: int


class ProofManager:
    def __init__(self) -> None:
        self._store: Dict[str, Proof] = {}

    def generate(self, kind: str, payload: Dict[str, Any]) -> Proof:
        created_ms = _now_epoch_ms()
        payload_hash = _blake2b_hex(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode())
        proof_id = _blake2b_hex(f"{kind}:{payload_hash}:{created_ms}".encode())
        proof = Proof(proof_id=proof_id, kind=kind, payload_hash=payload_hash, created_ms=created_ms)
        self._store[proof_id] = proof
        return proof

    def verify(self, proof: Proof, payload: Dict[str, Any]) -> bool:
        expected = _blake2b_hex(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode())
        return proof.payload_hash == expected and proof.proof_id in self._store

    def submit_on_chain(self, proofs: List[Proof], ledger_entry: Dict[str, Any]) -> str:
        material = {
            "proof_ids": [p.proof_id for p in proofs],
            "ledger_digest": _blake2b_hex(json.dumps(ledger_entry, sort_keys=True, separators=(",", ":")).encode()),
        }
        return _blake2b_hex(json.dumps(material, sort_keys=True, separators=(",", ":")).encode())
