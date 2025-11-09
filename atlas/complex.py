from __future__ import annotations
from typing import Generator, Iterable, Tuple

from .anchors import ANCHORS
from .symmetry import Involutions, gray11

class BoundaryComplex:
    """12,288‑cell boundary complex.

    Nodes are pairs (p,b) with p∈Z/48, b∈Z/256. The complex is the disjoint union
    of six 11‑cubes (one per anchor), i.e. each component has 2^11 nodes and degree 11.
    Adjacency: Hamming‑1 in the 11 involution bits.
    """

    def __init__(self) -> None:
        self.anchors = ANCHORS[:]  # six seeds

    def cell_from(self, anchor_index: int, gray_index: int) -> Tuple[int, int]:
        a = self.anchors[anchor_index % 6]
        g = gray11(gray_index % 2048)
        # Map Gray bits to flips relative to anchor
        b = (a[1] ^ (g & 0xFF)) % 256
        # Flip p2 low 3 bits by g>>8
        from .group import split_p, join_p
        p2, p3 = split_p(a[0])
        p2 ^= (g >> 8) & 0x7
        p = join_p(p2, p3) % 48
        return p, b

    def neighbors(self, anchor_index: int, gray_index: int) -> Generator[Tuple[int, int], None, None]:
        """Yield 11 neighbors by toggling one bit at a time."""
        a = anchor_index % 6
        g = gray_index % 2048
        for j in range(11):
            h = g ^ (1 << j)
            yield self.cell_from(a, h)

    def all_cells(self) -> Generator[Tuple[int, int], None, None]:
        for a in range(6):
            for g in range(2048):
                yield self.cell_from(a, g)
