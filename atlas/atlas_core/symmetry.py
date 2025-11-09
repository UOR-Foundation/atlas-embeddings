from __future__ import annotations
from dataclasses import dataclass
from typing import Iterable, List, Tuple

from .group import split_p, join_p

# Gray code on 11 bits

def gray11(i: int) -> int:
    return (int(i) & 0x7FF) ^ ((int(i) & 0x7FF) >> 1)

def ungray11(g: int) -> int:
    g &= 0x7FF
    x = g
    s = 1
    while (g >> s) > 0:
        x ^= (g >> s)
        s += 1
    return x & 0x7FF

@dataclass(frozen=True)
class Involutions:
    """(Z/2)^11 action via commuting bit‑flips on (p,b) in P×B.

    - 8 involutions flip the 8 bits of b (UInt8).
    - 3 involutions flip the low 3 bits of p2 in the decomposition p = p2 + 16 p3.
      p3 is fixed by the action and encodes the 3‑part of Z/48.
    The 11 flips commute and square to identity.
    """

    @staticmethod
    def apply(p: int, b: int, bit_index: int) -> Tuple[int, int]:
        if not (0 <= bit_index < 11):
            raise ValueError("bit_index must be in [0,11)")
        if bit_index < 8:
            # Flip bit in b
            b ^= (1 << bit_index)
            return p % 48, b % 256
        # Flip low 3 bits of p2
        p2, p3 = split_p(p)
        k = bit_index - 8  # 0..2 ↦ p2 bit 0..2
        p2 ^= (1 << k)
        return join_p(p2, p3) % 48, b % 256

    @staticmethod
    def apply_many(p: int, b: int, bits: Iterable[int]) -> Tuple[int, int]:
        for idx in bits:
            p, b = Involutions.apply(p, b, int(idx))
        return p, b

    @staticmethod
    def orbit_from_anchor(anchor_p: int, anchor_b: int) -> List[Tuple[int, int]]:
        """Enumerate the 2^11 orbit as Gray‑order for locality.
        Returns a list of 2048 distinct (p,b) pairs.
        """
        p0, b0 = anchor_p % 48, anchor_b % 256
        out: List[Tuple[int, int]] = []
        # Interpret Gray code bits: 0..7 map to b bits, 8..10 map to p2 bits 0..2
        for t in range(1 << 11):
            g = gray11(t)
            b = b0 ^ (g & 0xFF)
            p2, p3 = split_p(p0)
            p2 ^= (g >> 8) & 0x7
            out.append((join_p(p2, p3), b))
        # Sanity: uniqueness
        assert len(set(out)) == 2048
        return out
