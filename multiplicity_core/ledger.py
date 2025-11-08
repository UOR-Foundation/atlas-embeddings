"""
Atlas ⨯ MTPI — Local Ledger

Append-only in-node ledger with broadcast hooks.
Replace broadcast() with your node's pub-sub or event bus.
"""
from __future__ import annotations

import json
import time
import hashlib
from typing import Any, Dict, List


def _now_epoch_ms() -> int:
    return int(time.time() * 1000)


def _blake2b_hex(data: bytes) -> str:
    return hashlib.blake2b(data, digest_size=32).hexdigest()


class Ledger:
    def __init__(self):
        self._entries: List[Dict[str, Any]] = []

    def append(self, entry: Dict[str, Any]) -> str:
        entry = dict(entry)
        entry["entry_ms"] = _now_epoch_ms()
        entry["entry_id"] = _blake2b_hex(json.dumps(entry, sort_keys=True, separators=(",", ":")).encode())
        self._entries.append(entry)
        return entry["entry_id"]

    def broadcast(self, entry_id: str) -> None:
        # No-op stub. Wire to your messaging layer.
        return None

    @property
    def entries(self) -> List[Dict[str, Any]]:
        return list(self._entries)
