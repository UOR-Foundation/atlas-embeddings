"""
Functional API for PyTorch tensor operations using hologram.

Provides PyTorch-like functional operations that use hologram compute backend.
Operations maintain PyTorch's API while leveraging hologram's performance.

Example:
    >>> import torch
    >>> import hologram_torch as hg
    >>>
    >>> exec = hg.Executor()
    >>> a = torch.randn(1000)
    >>> b = torch.randn(1000)
    >>> c = hg.functional.add(exec, a, b)
"""

import torch
from typing import Optional
import hologram as hg
from .utils import tensor_to_buffer, buffer_to_tensor, validate_tensor_compatible


def add(
    executor: hg.Executor,
    input1: torch.Tensor,
    input2: torch.Tensor,
    out: Optional[torch.Tensor] = None
) -> torch.Tensor:
    """
    Element-wise addition using hologram: result = input1 + input2

    Args:
        executor: Hologram executor
        input1: First input tensor
        input2: Second input tensor
        out: Optional output tensor (must match input shape)

    Returns:
        Result tensor

    Example:
        >>> a = torch.tensor([1.0, 2.0, 3.0])
        >>> b = torch.tensor([4.0, 5.0, 6.0])
        >>> c = hg.functional.add(exec, a, b)
        >>> print(c)  # tensor([5., 7., 9.])
    """
    # Validate inputs
    validate_tensor_compatible(input1)
    validate_tensor_compatible(input2)

    if input1.shape != input2.shape:
        raise ValueError(
            f"Input shapes must match: {input1.shape} != {input2.shape}"
        )

    # Convert to buffers
    buf_a, flat_a = tensor_to_buffer(executor, input1)
    buf_b, flat_b = tensor_to_buffer(executor, input2)
    buf_c = executor.allocate(flat_a.numel())

    # Execute operation
    hg.ops.vector_add(executor, buf_a, buf_b, buf_c)

    # Convert back to tensor
    result = buffer_to_tensor(buf_c, input1.shape)

    if out is not None:
        out.copy_(result)
        return out

    return result


def mul(
    executor: hg.Executor,
    input1: torch.Tensor,
    input2: torch.Tensor,
    out: Optional[torch.Tensor] = None
) -> torch.Tensor:
    """Element-wise multiplication: result = input1 * input2"""
    validate_tensor_compatible(input1)
    validate_tensor_compatible(input2)

    if input1.shape != input2.shape:
        raise ValueError(f"Input shapes must match: {input1.shape} != {input2.shape}")

    buf_a, flat_a = tensor_to_buffer(executor, input1)
    buf_b, flat_b = tensor_to_buffer(executor, input2)
    buf_c = executor.allocate(flat_a.numel())

    hg.ops.vector_mul(executor, buf_a, buf_b, buf_c)

    result = buffer_to_tensor(buf_c, input1.shape)

    if out is not None:
        out.copy_(result)
        return out

    return result


def sub(
    executor: hg.Executor,
    input1: torch.Tensor,
    input2: torch.Tensor,
    out: Optional[torch.Tensor] = None
) -> torch.Tensor:
    """Element-wise subtraction: result = input1 - input2"""
    validate_tensor_compatible(input1)
    validate_tensor_compatible(input2)

    if input1.shape != input2.shape:
        raise ValueError(f"Input shapes must match: {input1.shape} != {input2.shape}")

    buf_a, flat_a = tensor_to_buffer(executor, input1)
    buf_b, flat_b = tensor_to_buffer(executor, input2)
    buf_c = executor.allocate(flat_a.numel())

    hg.ops.vector_sub(executor, buf_a, buf_b, buf_c)

    result = buffer_to_tensor(buf_c, input1.shape)

    if out is not None:
        out.copy_(result)
        return out

    return result


def relu(
    executor: hg.Executor,
    input: torch.Tensor,
    inplace: bool = False
) -> torch.Tensor:
    """
    ReLU activation: result = max(0, input)

    Args:
        executor: Hologram executor
        input: Input tensor
        inplace: If True, modify input tensor in-place

    Returns:
        Result tensor
    """
    validate_tensor_compatible(input)

    buf_a, flat_a = tensor_to_buffer(executor, input)
    buf_b = executor.allocate(flat_a.numel())

    hg.ops.vector_relu(executor, buf_a, buf_b)

    result = buffer_to_tensor(buf_b, input.shape)

    if inplace:
        input.copy_(result)
        return input

    return result


def sigmoid(
    executor: hg.Executor,
    input: torch.Tensor
) -> torch.Tensor:
    """Sigmoid activation: result = 1 / (1 + exp(-input))"""
    validate_tensor_compatible(input)

    buf_a, flat_a = tensor_to_buffer(executor, input)
    buf_b = executor.allocate(flat_a.numel())

    hg.ops.sigmoid(executor, buf_a, buf_b)

    return buffer_to_tensor(buf_b, input.shape)


def tanh(
    executor: hg.Executor,
    input: torch.Tensor
) -> torch.Tensor:
    """Hyperbolic tangent activation"""
    validate_tensor_compatible(input)

    buf_a, flat_a = tensor_to_buffer(executor, input)
    buf_b = executor.allocate(flat_a.numel())

    hg.ops.tanh(executor, buf_a, buf_b)

    return buffer_to_tensor(buf_b, input.shape)


def gelu(
    executor: hg.Executor,
    input: torch.Tensor
) -> torch.Tensor:
    """GELU activation"""
    validate_tensor_compatible(input)

    buf_a, flat_a = tensor_to_buffer(executor, input)
    buf_b = executor.allocate(flat_a.numel())

    hg.ops.gelu(executor, buf_a, buf_b)

    return buffer_to_tensor(buf_b, input.shape)


def softmax(
    executor: hg.Executor,
    input: torch.Tensor,
    dim: Optional[int] = None
) -> torch.Tensor:
    """
    Softmax activation

    Note: Currently operates on flattened tensor. Dimension support coming soon.
    """
    validate_tensor_compatible(input)

    if dim is not None:
        # TODO: Implement dimension-aware softmax in future
        raise NotImplementedError("Dimension-aware softmax coming soon")

    buf_a, flat_a = tensor_to_buffer(executor, input)
    buf_b = executor.allocate(flat_a.numel())

    hg.ops.softmax(executor, buf_a, buf_b)

    return buffer_to_tensor(buf_b, input.shape)


def linear(
    executor: hg.Executor,
    input: torch.Tensor,
    weight: torch.Tensor,
    bias: Optional[torch.Tensor] = None
) -> torch.Tensor:
    """
    Linear transformation: result = input @ weight.T + bias

    Args:
        executor: Hologram executor
        input: Input tensor (*, in_features)
        weight: Weight matrix (out_features, in_features)
        bias: Optional bias vector (out_features)

    Returns:
        Output tensor (*, out_features)
    """
    validate_tensor_compatible(input)
    validate_tensor_compatible(weight)

    # Flatten batch dimensions
    input_2d = input.view(-1, input.shape[-1])
    batch_size, in_features = input_2d.shape
    out_features, in_features_w = weight.shape

    if in_features != in_features_w:
        raise ValueError(
            f"Input features {in_features} doesn't match weight features {in_features_w}"
        )

    # Convert to buffers
    buf_input, _ = tensor_to_buffer(executor, input_2d)
    buf_weight, _ = tensor_to_buffer(executor, weight.T.contiguous())  # Transpose weight
    buf_output = executor.allocate(batch_size * out_features)

    # Matrix multiplication
    hg.ops.gemm(executor, buf_input, buf_weight, buf_output, batch_size, out_features, in_features)

    # Convert result
    result = buffer_to_tensor(buf_output, (batch_size, out_features))

    # Add bias if provided
    if bias is not None:
        validate_tensor_compatible(bias)
        result = result + bias.unsqueeze(0)

    # Reshape to match input batch dimensions
    output_shape = list(input.shape[:-1]) + [out_features]
    return result.view(*output_shape)


def mse_loss(
    executor: hg.Executor,
    input: torch.Tensor,
    target: torch.Tensor,
    reduction: str = 'mean'
) -> torch.Tensor:
    """
    Mean Squared Error loss

    Args:
        executor: Hologram executor
        input: Predictions tensor
        target: Targets tensor
        reduction: 'mean', 'sum', or 'none' (default: 'mean')

    Returns:
        Loss value
    """
    validate_tensor_compatible(input)
    validate_tensor_compatible(target)

    if input.shape != target.shape:
        raise ValueError(f"Input and target shapes must match: {input.shape} != {target.shape}")

    buf_input, flat_input = tensor_to_buffer(executor, input)
    buf_target, flat_target = tensor_to_buffer(executor, target)
    buf_output = executor.allocate(3)  # Need 3 elements for temporaries

    loss_val = hg.ops.mse_loss(executor, buf_input, buf_target, buf_output)

    if reduction == 'none':
        # Return per-element losses (not yet implemented)
        raise NotImplementedError("reduction='none' not yet implemented")
    elif reduction == 'sum':
        return torch.tensor(loss_val * flat_input.numel())
    else:  # mean
        return torch.tensor(loss_val)


# Convenience aliases
__all__ = [
    "add",
    "mul",
    "sub",
    "relu",
    "sigmoid",
    "tanh",
    "gelu",
    "softmax",
    "linear",
    "mse_loss",
]
