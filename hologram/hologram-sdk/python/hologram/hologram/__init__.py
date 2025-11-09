"""
Hologram Python Bindings

Pythonic wrapper around hologram-ffi providing automatic resource management,
zero-copy operations, and seamless NumPy integration.

Example:
    >>> import hologram as hg
    >>> import numpy as np
    >>>
    >>> with hg.Executor() as exec:
    ...     buf_a = exec.allocate(1024)
    ...     buf_b = exec.allocate(1024)
    ...     buf_c = exec.allocate(1024)
    ...
    ...     data_a = np.random.randn(1024).astype(np.float32)
    ...     data_b = np.random.randn(1024).astype(np.float32)
    ...
    ...     buf_a.from_numpy(data_a)
    ...     buf_b.from_numpy(data_b)
    ...
    ...     hg.ops.vector_add(exec, buf_a, buf_b, buf_c, 1024)
    ...
    ...     result = buf_c.to_numpy()
    ...     print(f"Result: {result[:5]}")
"""

__version__ = "0.1.0"

# Core components
from .executor import Executor
from .buffer import Buffer
from . import ops
from . import backend

# Re-export backend utilities for convenience
from .backend import BackendType, is_metal_available, is_cuda_available, get_default_backend

# Re-export for convenience
__all__ = [
    # Core classes
    "Executor",
    "Buffer",
    # Modules
    "ops",
    "backend",
    # Backend utilities
    "BackendType",
    "is_metal_available",
    "is_cuda_available",
    "get_default_backend",
    # Metadata
    "__version__",
]
