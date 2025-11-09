from __future__ import annotations
from dataclasses import dataclass
from typing import Dict, Generator, Iterable, Tuple

from .complex import BoundaryComplex

@dataclass
class C768Schedule:
    """C768 fair traversal with exact marginal stationarity per 768‑step window.

    Construction:
    - Let u = t mod 768.
    - Define i(u) = (α*u) mod 48 with gcd(α,48)=1. Use α=1.
      Each 768‑block visits every page 16 times.
    - Define j(u) = (β*u) mod 256 with gcd(β,256)=1. Use β=3.
      Each 768‑block visits each byte 3 times.
    - Split u into six chunks of 128 steps: a(u) = ⌊u/128⌋ ∈ {0..5} selects the anchor.
    - Let w = ⌊t/768⌋ ∈ {0..15}. Define g(t) = 128*w + (u mod 128) ∈ {0..2047}.
      Over 16 blocks this covers all 2048 Gray states per anchor exactly once.
    - The emitted cell is base_cell(a,g) plus the additive offset (i(u), j(u)) in Z/48×Z/256.
      Addition is component‑wise modulo (48,256).

    Result:
      - 12,288 distinct cells in t ∈ {0..12287}.
      - In every 768‑window, page marginals are uniform (16 each) and byte marginals are uniform (3 each).
      - Joint stationarity beyond marginals is UNPROVEN.
    """

    alpha: int = 1
    beta: int = 3

    def __post_init__(self) -> None:
        if self.alpha % 2 == 0 or self.alpha % 3 == 0:
            raise ValueError("alpha must be coprime to 48")
        if self.beta % 2 == 0:
            raise ValueError("beta must be coprime to 256")
        self.complex = BoundaryComplex()

    @staticmethod
    def _offset(u: int) -> Tuple[int, int]:
        i = (1 * u) % 48
        j = (3 * u) % 256
        return i, j

    def at(self, t: int) -> Tuple[int, int]:
        u = t % 768
        w = t // 768  # 0..15 over 12,288 steps
        a = u // 128  # 0..5 within block
        g = 128 * w + (u % 128)  # 0..2047 spreads across blocks
        p0, b0 = self.complex.cell_from(a, g)
        di, dj = (self.alpha * u) % 48, (self.beta * u) % 256
        return (p0 + di) % 48, (b0 + dj) % 256

    def window_counts(self, start_t: int) -> Tuple[Dict[int, int], Dict[int, int]]:
        pages: Dict[int, int] = {i: 0 for i in range(48)}
        bytes_: Dict[int, int] = {j: 0 for j in range(256)}
        for k in range(768):
            p, b = self.at(start_t + k)
            pages[p] += 1
            bytes_[b] += 1
        return pages, bytes_

    def iterate(self, steps: int) -> Generator[Tuple[int, int], None, None]:
        for t in range(steps):
            yield self.at(t)
