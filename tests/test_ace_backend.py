"""
Tests for ACE backend selector.
"""
import os
from multiplicity_core.ace_backend import select_xp


def test_default_numpy_backend():
    """Test default backend is numpy."""
    xp, np, is_gpu = select_xp()
    assert not is_gpu
    assert xp.__name__ == "numpy"
    assert np.__name__ == "numpy"


def test_explicit_numpy_backend():
    """Test explicit numpy backend."""
    xp, np, is_gpu = select_xp(backend="numpy")
    assert not is_gpu
    assert xp.__name__ == "numpy"


def test_explicit_cupy_fallback():
    """Test cupy backend falls back to numpy when cupy is not available."""
    # This will likely fallback unless cupy is installed
    xp, np, is_gpu = select_xp(backend="cupy")
    # Either cupy works or it falls back to numpy
    assert xp.__name__ in ["numpy", "cupy"]
    if is_gpu:
        assert xp.__name__ == "cupy"
    else:
        assert xp.__name__ == "numpy"


def test_env_var_backend(monkeypatch):
    """Test backend selection via environment variable."""
    monkeypatch.setenv("ACE_BACKEND", "numpy")
    xp, np, is_gpu = select_xp()
    assert not is_gpu
    assert xp.__name__ == "numpy"


def test_invalid_backend_defaults_to_numpy():
    """Test invalid backend defaults to numpy."""
    xp, np, is_gpu = select_xp(backend="invalid")
    assert not is_gpu
    assert xp.__name__ == "numpy"
