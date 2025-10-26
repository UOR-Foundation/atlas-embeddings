"""
GG architecture: torus Z_96 x Z_128, budget semiring B96, schedule order 768.
"""
from typing import Tuple, Iterator

def torus_point(a: int, b: int) -> Tuple[int, int]:
    return (a % 96, b % 128)

def oplus(x: int, y: int) -> int:
    """Saturating add on B96. TODO."""
    raise NotImplementedError

def otimes(x: int, y: int) -> int:
    """Saturating multiply on B96. TODO."""
    raise NotImplementedError

def schedule(seed: int) -> Iterator[Tuple[int,int]]:
    """Yield a schedule with group order 768. TODO."""
    raise NotImplementedError
