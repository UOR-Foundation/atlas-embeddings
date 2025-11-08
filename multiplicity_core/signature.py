from __future__ import annotations
from hashlib import sha256
from typing import Any
import json

def digest(obj: Any) -> str:
    """Deterministic SHA‑256 of a JSON‑serializable object."""
    s = json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return sha256(s.encode("utf-8")).hexdigest()
