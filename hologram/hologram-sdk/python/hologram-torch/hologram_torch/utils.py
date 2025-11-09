"""
Utility functions for PyTorch tensor conversions.

Provides helper functions for converting between PyTorch tensors and hologram buffers
with minimal copying where possible.
"""

import torch
import numpy as np
from typing import Tuple, Optional
import hologram as hg


def tensor_to_buffer(
    executor: hg.Executor,
    tensor: torch.Tensor,
    existing_buffer: Optional[hg.Buffer] = None
) -> Tuple[hg.Buffer, torch.Tensor]:
    """
    Convert PyTorch tensor to hologram buffer (zero-copy when possible).

    Args:
        executor: Hologram executor
        tensor: PyTorch tensor (must be float32, contiguous, on CPU)
        existing_buffer: Optional existing buffer to reuse

    Returns:
        Tuple of (buffer, flattened_tensor)

    Raises:
        ValueError: If tensor is not compatible
    """
    # Validate tensor
    if not isinstance(tensor, torch.Tensor):
        raise TypeError(f"Expected torch.Tensor, got {type(tensor)}")

    if tensor.dtype != torch.float32:
        raise ValueError(f"Only float32 tensors supported, got {tensor.dtype}")

    if tensor.device.type != 'cpu':
        raise ValueError(
            f"Only CPU tensors supported for now, got device '{tensor.device}'. "
            f"Move tensor to CPU first: tensor.cpu()"
        )

    # Flatten tensor
    flat_tensor = tensor.contiguous().view(-1)
    size = flat_tensor.numel()

    # Allocate buffer if needed
    if existing_buffer is None:
        buffer = executor.allocate(size)
    else:
        if existing_buffer.size != size:
            raise ValueError(
                f"Existing buffer size {existing_buffer.size} doesn't match tensor size {size}"
            )
        buffer = existing_buffer

    # Convert to NumPy and copy to buffer (zero-copy where possible)
    numpy_array = flat_tensor.detach().numpy()
    buffer.from_numpy(numpy_array)

    return buffer, flat_tensor


def buffer_to_tensor(
    buffer: hg.Buffer,
    shape: Tuple[int, ...],
    device: torch.device = torch.device('cpu'),
    requires_grad: bool = False
) -> torch.Tensor:
    """
    Convert hologram buffer to PyTorch tensor (zero-copy when possible).

    Args:
        buffer: Hologram buffer
        shape: Desired tensor shape
        device: PyTorch device (currently only CPU supported)
        requires_grad: Whether tensor should require gradients

    Returns:
        PyTorch tensor with specified shape

    Raises:
        ValueError: If shape doesn't match buffer size or device is not CPU
    """
    # Validate shape
    numel = int(np.prod(shape))
    if numel != buffer.size:
        raise ValueError(
            f"Shape {shape} (numel={numel}) doesn't match buffer size {buffer.size}"
        )

    # Only CPU supported for now
    if device.type != 'cpu':
        raise ValueError(f"Only CPU device supported for now, got {device}")

    # Read buffer to NumPy (zero-copy)
    numpy_array = buffer.to_numpy()

    # Create PyTorch tensor from NumPy (zero-copy)
    tensor = torch.from_numpy(numpy_array).reshape(shape)

    if requires_grad:
        tensor = tensor.requires_grad_(True)

    return tensor


def validate_tensor_compatible(tensor: torch.Tensor) -> None:
    """
    Validate that tensor is compatible with hologram operations.

    Args:
        tensor: PyTorch tensor to validate

    Raises:
        ValueError: If tensor is not compatible
    """
    if not isinstance(tensor, torch.Tensor):
        raise TypeError(f"Expected torch.Tensor, got {type(tensor)}")

    if tensor.dtype != torch.float32:
        raise ValueError(
            f"Only float32 tensors supported, got {tensor.dtype}. "
            f"Convert with: tensor.float()"
        )

    if tensor.device.type != 'cpu':
        raise ValueError(
            f"Only CPU tensors supported for now, got device '{tensor.device}'. "
            f"Move to CPU with: tensor.cpu()"
        )


def match_device(
    tensor: torch.Tensor,
    backend: Optional[str] = None
) -> str:
    """
    Match PyTorch tensor device to hologram backend.

    Args:
        tensor: PyTorch tensor
        backend: Optional backend override

    Returns:
        Backend string ('cpu', 'metal', 'cuda')
    """
    if backend is not None:
        return backend

    # Auto-detect from tensor device
    if tensor.device.type == 'cpu':
        return 'cpu'
    elif tensor.device.type == 'cuda':
        return 'cuda'
    elif tensor.device.type == 'mps':  # Apple Metal Performance Shaders
        return 'metal'
    else:
        # Unknown device, default to CPU
        return 'cpu'


def create_executor_for_tensor(
    tensor: torch.Tensor,
    backend: Optional[str] = None
) -> hg.Executor:
    """
    Create hologram executor matching PyTorch tensor's device.

    Args:
        tensor: PyTorch tensor
        backend: Optional backend override

    Returns:
        Hologram executor

    Example:
        >>> tensor = torch.randn(100).cuda()  # On GPU
        >>> exec = create_executor_for_tensor(tensor)  # Creates CUDA executor
    """
    backend_str = match_device(tensor, backend)
    return hg.Executor(backend=backend_str)
