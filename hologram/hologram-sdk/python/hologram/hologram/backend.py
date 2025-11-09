"""
Backend utilities for hologram execution.

Provides backend type enumeration and detection utilities.
"""

from enum import Enum
from typing import Optional


class BackendType(Enum):
    """Backend types for hologram execution."""

    CPU = "cpu"
    METAL = "metal"
    CUDA = "cuda"
    AUTO = "auto"

    def __str__(self) -> str:
        return self.value


def is_metal_available() -> bool:
    """
    Check if Metal backend is available (Apple Silicon).

    Returns:
        True if on macOS with Apple Silicon, False otherwise.
    """
    import platform
    import sys

    return (
        sys.platform == "darwin" and
        platform.machine() == "arm64"
    )


def is_cuda_available() -> bool:
    """
    Check if CUDA backend is available (NVIDIA GPU).

    Returns:
        True if CUDA is available, False otherwise.

    Note:
        Checks for CUDA by attempting to query nvidia-smi.
        Requires 'cuda' feature to be enabled in hologram-core build.
    """
    import subprocess
    import os

    # Check if nvidia-smi exists and can detect GPU
    try:
        result = subprocess.run(
            ['nvidia-smi', '-L'],
            capture_output=True,
            timeout=1,
            env={**os.environ, 'LANG': 'C'}
        )
        # If nvidia-smi succeeds and finds at least one GPU
        return result.returncode == 0 and b'GPU' in result.stdout
    except (FileNotFoundError, subprocess.TimeoutExpired, Exception):
        return False


def get_default_backend() -> str:
    """
    Get the default backend based on available hardware.

    Returns best available backend in order:
    1. Metal (if on Apple Silicon)
    2. CUDA (if NVIDIA GPU available)
    3. CPU (fallback, always available)

    Returns:
        Backend string: "metal", "cuda", or "cpu"
    """
    if is_metal_available():
        return "metal"
    elif is_cuda_available():
        return "cuda"
    else:
        return "cpu"


def validate_backend(backend: str) -> str:
    """
    Validate and normalize backend string.

    Args:
        backend: Backend string ("cpu", "metal", "cuda", "auto")

    Returns:
        Normalized backend string

    Raises:
        ValueError: If backend is invalid
    """
    backend_lower = backend.lower()

    if backend_lower == "auto":
        return get_default_backend()

    valid_backends = {"cpu", "metal", "cuda"}
    if backend_lower not in valid_backends:
        raise ValueError(
            f"Invalid backend '{backend}'. "
            f"Must be one of: {', '.join(valid_backends)}, or 'auto'"
        )

    return backend_lower
