"""
Backend selector for ACE: numpy or cupy.
Choose via env ACE_BACKEND={numpy|cupy} or by passing backend="cupy".
Exports select_xp(backend:str|None)->(xp,np,is_gpu)
"""
from __future__ import annotations

import os
import sys
from typing import Tuple


def _get_real_numpy():
    """Get real numpy package, not the local stub."""
    # Temporarily filter sys.path to avoid local numpy stub
    _repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    _original_path = sys.path.copy()
    sys.path = [p for p in sys.path if p != _repo_root and not p.endswith('/atlas-hologram')]
    try:
        import numpy as _real_np
        return _real_np
    finally:
        sys.path = _original_path


def select_xp(backend: str | None = None) -> Tuple:
    """Select backend (numpy or cupy) and return (xp, np, is_gpu).
    
    Args:
        backend: "numpy" or "cupy". If None, uses ACE_BACKEND env var (defaults to "numpy")
    
    Returns:
        Tuple of (xp, np, is_gpu) where:
        - xp is the primary array library (cupy or numpy)
        - np is always numpy (for host operations)
        - is_gpu is True if cupy is active
    """
    b = (backend or os.environ.get("ACE_BACKEND", "numpy")).strip().lower()
    if b == "cupy":
        try:
            import cupy as xp  # type: ignore
            np = _get_real_numpy()
            return xp, np, True
        except Exception:  # fallback to numpy
            np = _get_real_numpy()
            xp = np
            return xp, np, False
    else:
        xp = _get_real_numpy()
        np = xp
        return xp, np, False
