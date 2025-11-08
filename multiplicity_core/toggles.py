from __future__ import annotations
from dataclasses import dataclass, field
from typing import Dict, List

@dataclass
class ToggleStreams:
    """Toggle streams E: ℕ → B*.

    For each lane n we store a finite or infinite boolean schedule. is_on(n, t) gates updates.
    Missing schedules default to True (always on)."""

    schedules: Dict[int, List[bool]] = field(default_factory=dict)

    def set_schedule(self, n: int, bits: List[bool]) -> None:
        self.schedules[n] = list(bool(x) for x in bits)

    def is_on(self, n: int, t: int) -> bool:
        bits = self.schedules.get(n)
        if not bits:
            return True
        idx = t % len(bits)
        return bool(bits[idx])
