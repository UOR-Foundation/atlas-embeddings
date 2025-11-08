from __future__ import annotations
from dataclasses import dataclass
from typing import Iterable, List

@dataclass
class Z96Quantizer:
    """Quantizer q: R* → C with C = Z_96.

    y = round(scale * x + offset) mod 96
    - scale > 0
    - offset in R (bias)
    """

    scale: float = 1.0
    offset: float = 0.0

    def quantize(self, x: float) -> int:
        y = int(round(self.scale * float(x) + self.offset))
        return y % 96

    def quantize_all(self, xs: Iterable[float]) -> List[int]:
        return [self.quantize(x) for x in xs]

    def decode(self, z: int) -> float:
        """Inverse up to modulo 96 periodicity.
        Returns the principal representative with k = 0: (z - offset)/scale.
        """
        return (int(z) - self.offset) / self.scale
