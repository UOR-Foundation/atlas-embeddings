from __future__ import annotations
from dataclasses import dataclass, field, asdict
from hashlib import sha256
from typing import Any, Dict, List, Optional
import json
import time

@dataclass
class LedgerRow:
    op: str
    payload_digest: str
    prev_digest: str
    timestamp: float
    digest: str

@dataclass
class PETCLedger:
    """Prime‑Exact Tensor Consistency (PETC) ledger.

    Per‑operation signature chain over canonical JSON payloads.
    """
    rows: List[LedgerRow] = field(default_factory=list)

    @staticmethod
    def _canon(obj: Any) -> str:
        return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)

    @staticmethod
    def _h(s: str) -> str:
        return sha256(s.encode("utf-8")).hexdigest()

    def append(self, op: str, payload: Dict[str, Any], ts: Optional[float] = None) -> LedgerRow:
        body = {"op": op, "payload": payload}
        pdig = self._h(self._canon(body))
        prev = self.rows[-1].digest if self.rows else "0" * 64
        t = float(ts if ts is not None else time.time())
        digest = self._h(self._canon({"pdig": pdig, "prev": prev, "t": t}))
        row = LedgerRow(op=op, payload_digest=pdig, prev_digest=prev, timestamp=t, digest=digest)
        self.rows.append(row)
        return row

    def verify(self) -> bool:
        prev = "0" * 64
        for r in self.rows:
            recomputed = self._h(self._canon({"pdig": r.payload_digest, "prev": prev, "t": r.timestamp}))
            if recomputed != r.digest:
                return False
            prev = r.digest
        return True
