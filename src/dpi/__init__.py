"""
DPI compressors on Z_m with Fourier TV bounds and MI control.
"""
from typing import Dict, Any


def compress(x, m: int):
    raise NotImplementedError


def tv_bound(x, m: int) -> float:
    raise NotImplementedError


def mi_estimate(a, b) -> float:
    raise NotImplementedError


def checklist(m: int) -> Dict[str, Any]:
    """Return per-modulus checklist results. TODO."""
    raise NotImplementedError
