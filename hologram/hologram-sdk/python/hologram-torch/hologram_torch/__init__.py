"""
Hologram PyTorch Integration

PyTorch integration for hologram compute acceleration providing:
- Functional API (hologram_torch.functional)
- nn.Module wrappers (hologram_torch.nn)
- Automatic tensor conversion
- Zero-copy operations where possible

Example - Functional API:
    >>> import torch
    >>> import hologram_torch as hg
    >>>
    >>> exec = hg.Executor()
    >>> a = torch.randn(1000)
    >>> b = torch.randn(1000)
    >>> c = hg.functional.add(exec, a, b)

Example - Module API:
    >>> import torch
    >>> import hologram_torch as hg
    >>>
    >>> model = torch.nn.Sequential(
    ...     hg.nn.Linear(128, 64),
    ...     hg.nn.ReLU(),
    ...     hg.nn.Linear(64, 10)
    ... )
    >>> x = torch.randn(32, 128)
    >>> y = model(x)
"""

__version__ = "0.1.0"

# Re-export from hologram for convenience
from hologram import Executor, Buffer, BackendType

# Import submodules
from . import functional
from . import nn
from . import utils

# Convenience imports
from .utils import (
    tensor_to_buffer,
    buffer_to_tensor,
    validate_tensor_compatible,
    match_device,
    create_executor_for_tensor,
)

__all__ = [
    # Core (from hologram)
    "Executor",
    "Buffer",
    "BackendType",
    # Submodules
    "functional",
    "nn",
    "utils",
    # Utilities
    "tensor_to_buffer",
    "buffer_to_tensor",
    "validate_tensor_compatible",
    "match_device",
    "create_executor_for_tensor",
    # Metadata
    "__version__",
]
