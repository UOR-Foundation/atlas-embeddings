from __future__ import annotations
from typing import Dict, List

# Z_96 classification—consistent with Python and Rust references.

R96 = 96

def classify_byte_mod96(b: int) -> int:
    return int(b) % R96

def z96_distribution() -> Dict[int, int]:
    counts: Dict[int, int] = {i: 0 for i in range(R96)}
    for b in range(256):
        counts[classify_byte_mod96(b)] += 1
    return counts

def heavy_vs_light_classes() -> List[int]:
    """Return the classes that occur 3 times when mapping 0..255 → Z96.
    There are 64 heavy classes with count 3, and 32 light classes with count 2.
    """
    dist = z96_distribution()
    return [k for k, v in dist.items() if v == 3]
