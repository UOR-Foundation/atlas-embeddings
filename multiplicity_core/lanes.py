from __future__ import annotations
from dataclasses import dataclass, field
from typing import Dict, Hashable, Optional

ClassID = Hashable
LaneIndex = int

@dataclass
class LaneBuffer:
    """Holds a single lane's values per class.

    Values are arbitrary Python ints by default (moonshine c_n(g) coefficients)."""
    values: Dict[ClassID, int] = field(default_factory=dict)

    def get(self, cls: ClassID, default: int = 0) -> int:
        return int(self.values.get(cls, default))

    def set(self, cls: ClassID, value: int) -> None:
        self.values[cls] = int(value)

@dataclass
class MultiClassLaneStore:
    """Lane store with one lane per integer index n and per‑class buffers.

    - Provides O(1) access per lane/class.
    - Supports switching the active class at runtime without copying lanes.
    """
    active_class: ClassID
    _lanes: Dict[LaneIndex, LaneBuffer] = field(default_factory=dict)

    def ensure(self, n: LaneIndex) -> LaneBuffer:
        if n not in self._lanes:
            self._lanes[n] = LaneBuffer()
        return self._lanes[n]

    def write(self, n: LaneIndex, value: int, cls: Optional[ClassID] = None) -> None:
        buf = self.ensure(n)
        buf.set(self.active_class if cls is None else cls, value)

    def read(self, n: LaneIndex, cls: Optional[ClassID] = None, default: int = 0) -> int:
        buf = self.ensure(n)
        return buf.get(self.active_class if cls is None else cls, default)

    def switch_class(self, new_class: ClassID) -> None:
        self.active_class = new_class

    def snapshot_class(self, cls: Optional[ClassID] = None) -> Dict[LaneIndex, int]:
        c = self.active_class if cls is None else cls
        return {n: lb.get(c, 0) for n, lb in self._lanes.items()}

    def clear_class(self, cls: Optional[ClassID] = None) -> None:
        c = self.active_class if cls is None else cls
        for lb in self._lanes.values():
            if c in lb.values:
                del lb.values[c]
