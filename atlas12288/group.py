from __future__ import annotations
from typing import Tuple

# Group moduli
P_MOD = 48  # pages
B_MOD = 256 # bytes

# Decompose p ∈ Z/48 as p = p2 + 16 * p3 with p2 ∈ Z/16, p3 ∈ Z/3

def split_p(p: int) -> Tuple[int, int]:
    p = int(p) % P_MOD
    p3 = (p // 16) % 3
    p2 = p - 16 * p3
    return p2, p3

def join_p(p2: int, p3: int) -> int:
    return (int(p2) % 16) + 16 * (int(p3) % 3)

# Bit helpers

def get_bits(x: int, n: int) -> Tuple[int, ...]:
    return tuple((x >> i) & 1 for i in range(n))

def set_bits(bits: Tuple[int, ...]) -> int:
    v = 0
    for i, b in enumerate(bits):
        if b:
            v |= (1 << i)
    return v
