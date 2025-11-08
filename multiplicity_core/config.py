from __future__ import annotations
from dataclasses import dataclass

@dataclass
class RuntimeConfig:
    scale: float = 1.0
    offset: float = 0.0
