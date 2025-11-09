"""
PyTorch nn.Module wrappers for hologram operations.

Provides drop-in replacements for common PyTorch layers that use hologram backend.

Example:
    >>> import torch
    >>> import hologram_torch as hg
    >>>
    >>> model = torch.nn.Sequential(
    ...     hg.nn.Linear(128, 64),
    ...     hg.nn.ReLU(),
    ...     hg.nn.Linear(64, 10)
    ... )
"""

import torch
import torch.nn as nn
from typing import Optional
import hologram as hg
from . import functional as F


class ReLU(nn.Module):
    """
    ReLU activation module using hologram backend.

    Drop-in replacement for torch.nn.ReLU.

    Example:
        >>> relu = hg.nn.ReLU()
        >>> x = torch.randn(100)
        >>> y = relu(x)
    """

    def __init__(self, inplace: bool = False):
        """
        Initialize ReLU module.

        Args:
            inplace: If True, modify input tensor in-place
        """
        super().__init__()
        self.inplace = inplace
        self.executor = hg.Executor()  # Create executor for this module

    def forward(self, input: torch.Tensor) -> torch.Tensor:
        """Apply ReLU activation."""
        return F.relu(self.executor, input, inplace=self.inplace)

    def extra_repr(self) -> str:
        """Extra representation for print()."""
        return f"inplace={self.inplace}"


class Sigmoid(nn.Module):
    """Sigmoid activation module using hologram backend."""

    def __init__(self):
        super().__init__()
        self.executor = hg.Executor()

    def forward(self, input: torch.Tensor) -> torch.Tensor:
        """Apply sigmoid activation."""
        return F.sigmoid(self.executor, input)


class Tanh(nn.Module):
    """Hyperbolic tangent activation module using hologram backend."""

    def __init__(self):
        super().__init__()
        self.executor = hg.Executor()

    def forward(self, input: torch.Tensor) -> torch.Tensor:
        """Apply tanh activation."""
        return F.tanh(self.executor, input)


class GELU(nn.Module):
    """GELU activation module using hologram backend."""

    def __init__(self):
        super().__init__()
        self.executor = hg.Executor()

    def forward(self, input: torch.Tensor) -> torch.Tensor:
        """Apply GELU activation."""
        return F.gelu(self.executor, input)


class Softmax(nn.Module):
    """
    Softmax activation module using hologram backend.

    Note: dim parameter currently not supported. Coming soon.
    """

    def __init__(self, dim: Optional[int] = None):
        super().__init__()
        self.dim = dim
        self.executor = hg.Executor()

        if dim is not None:
            import warnings
            warnings.warn(
                "Dimension-aware softmax not yet supported in hologram. "
                "Operating on flattened tensor.",
                UserWarning
            )

    def forward(self, input: torch.Tensor) -> torch.Tensor:
        """Apply softmax activation."""
        return F.softmax(self.executor, input, dim=self.dim)

    def extra_repr(self) -> str:
        """Extra representation for print()."""
        return f"dim={self.dim}"


class Linear(nn.Module):
    """
    Linear transformation module using hologram backend.

    Drop-in replacement for torch.nn.Linear.

    Args:
        in_features: Size of input features
        out_features: Size of output features
        bias: If True, add learnable bias (default: True)

    Example:
        >>> linear = hg.nn.Linear(128, 64)
        >>> x = torch.randn(32, 128)  # (batch_size, in_features)
        >>> y = linear(x)              # (batch_size, out_features)
        >>> print(y.shape)             # torch.Size([32, 64])
    """

    def __init__(
        self,
        in_features: int,
        out_features: int,
        bias: bool = True,
        device=None,
        dtype=None
    ):
        super().__init__()
        self.in_features = in_features
        self.out_features = out_features

        # Initialize parameters (same as torch.nn.Linear)
        self.weight = nn.Parameter(torch.empty((out_features, in_features)))
        if bias:
            self.bias = nn.Parameter(torch.empty(out_features))
        else:
            self.register_parameter('bias', None)

        self.reset_parameters()
        self.executor = hg.Executor()

    def reset_parameters(self) -> None:
        """Reset parameters (same initialization as torch.nn.Linear)."""
        nn.init.kaiming_uniform_(self.weight, a=5**0.5)
        if self.bias is not None:
            fan_in, _ = nn.init._calculate_fan_in_and_fan_out(self.weight)
            bound = 1 / (fan_in ** 0.5) if fan_in > 0 else 0
            nn.init.uniform_(self.bias, -bound, bound)

    def forward(self, input: torch.Tensor) -> torch.Tensor:
        """
        Apply linear transformation.

        Args:
            input: Input tensor (*, in_features)

        Returns:
            Output tensor (*, out_features)
        """
        return F.linear(self.executor, input, self.weight, self.bias)

    def extra_repr(self) -> str:
        """Extra representation for print()."""
        return f"in_features={self.in_features}, out_features={self.out_features}, bias={self.bias is not None}"


class MSELoss(nn.Module):
    """
    Mean Squared Error loss module using hologram backend.

    Drop-in replacement for torch.nn.MSELoss.

    Args:
        reduction: 'mean', 'sum', or 'none' (default: 'mean')

    Example:
        >>> criterion = hg.nn.MSELoss()
        >>> pred = torch.randn(100)
        >>> target = torch.randn(100)
        >>> loss = criterion(pred, target)
    """

    def __init__(self, reduction: str = 'mean'):
        super().__init__()
        if reduction not in ['none', 'mean', 'sum']:
            raise ValueError(f"Invalid reduction mode: {reduction}")
        self.reduction = reduction
        self.executor = hg.Executor()

    def forward(self, input: torch.Tensor, target: torch.Tensor) -> torch.Tensor:
        """
        Compute MSE loss.

        Args:
            input: Predictions tensor
            target: Targets tensor

        Returns:
            Loss value
        """
        return F.mse_loss(self.executor, input, target, reduction=self.reduction)

    def extra_repr(self) -> str:
        """Extra representation for print()."""
        return f"reduction={self.reduction}"


# Convenience exports
__all__ = [
    "ReLU",
    "Sigmoid",
    "Tanh",
    "GELU",
    "Softmax",
    "Linear",
    "MSELoss",
]
