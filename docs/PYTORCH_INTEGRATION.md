# PyTorch + Hologram Runtime Integration Guide

## Overview

This guide demonstrates how to integrate the Hologram runtime with PyTorch for high-performance neural network computations. The Hologram runtime uses Sigmatics canonical circuit compilation to provide zero-interpretation compute acceleration on the 96-class system.

## Key Features

- **Zero-Interpretation Execution**: Pre-compiled native binary kernels
- **96-Class System**: Cache-resident 1.125 MiB boundary pool
- **Canonical Compilation**: Automatic operation reduction (typically 75%)
- **Low Latency**: ~100-500ns per operation vs ~5-6µs with runtime interpretation
- **PyTorch Compatibility**: Seamless integration with PyTorch models and tensors

## Architecture

```
PyTorch Model → Convert to Hologram Buffers → Execute on 96-Class System → Return Results
```

### Execution Model

1. **PyTorch Layer**: Define model using PyTorch's familiar API
2. **Buffer Conversion**: Convert PyTorch tensors to Hologram buffers
3. **Execute Operations**: Use Hologram's vectorized operations on 96-class system
4. **Result Retrieval**: Convert results back to PyTorch tensors

## Installation

### Prerequisites

1. **Install PyTorch**:

```bash
pip install torch
```

2. **Install Hologram FFI Python bindings**:

```bash
cd crates/hologram-ffi/interfaces/python
pip install -e .
```

3. **Build Hologram Runtime**:

```bash
cd ../..
cargo build --release
```

## Basic Usage

### Vector Addition Example

```python
import hologram_ffi as hg
import json

# Create executor
exec_handle = hg.new_executor()

# Allocate buffers
size = 1000
a_handle = hg.executor_allocate_buffer(exec_handle, size)
b_handle = hg.executor_allocate_buffer(exec_handle, size)
c_handle = hg.executor_allocate_buffer(exec_handle, size)

# Prepare data
data_a = [float(i) for i in range(size)]
data_b = [float(i * 2) for i in range(size)]

# Copy to buffers
hg.buffer_copy_from_slice(exec_handle, a_handle, json.dumps(data_a))
hg.buffer_copy_from_slice(exec_handle, b_handle, json.dumps(data_b))

# Execute vector addition
hg.vector_add_f32(exec_handle, a_handle, b_handle, c_handle, size)

# Read results
result_json = hg.buffer_to_vec(exec_handle, c_handle)
result = json.loads(result_json)

print(f"Result: {result[:10]}")  # First 10 elements

# Cleanup
hg.buffer_cleanup(a_handle)
hg.buffer_cleanup(b_handle)
hg.buffer_cleanup(c_handle)
hg.executor_cleanup(exec_handle)
```

## Available Operations

### Mathematical Operations

- `vector_add_f32`: Element-wise addition (c = a + b)
- `vector_sub_f32`: Element-wise subtraction (c = a - b)
- `vector_mul_f32`: Element-wise multiplication (c = a \* b)
- `vector_div_f32`: Element-wise division (c = a / b)
- `vector_min_f32`: Element-wise minimum (c = min(a, b))
- `vector_max_f32`: Element-wise maximum (c = max(a, b))
- `vector_abs_f32`: Element-wise absolute value (c = |a|)
- `vector_neg_f32`: Element-wise negation (c = -a)
- `vector_relu_f32`: ReLU activation (c = max(0, a))

### Activation Functions

- `sigmoid_f32`: Sigmoid activation
- `tanh_f32`: Hyperbolic tangent
- `gelu_f32`: GELU activation
- `softmax_f32`: Softmax normalization

### Reduction Operations

- `reduce_sum_f32`: Sum all elements (returns single value)
- `reduce_min_f32`: Minimum value (returns single value)
- `reduce_max_f32`: Maximum value (returns single value)

### Loss Functions

- `mse_loss_f32`: Mean Squared Error
- `cross_entropy_loss_f32`: Cross Entropy Loss
- `binary_cross_entropy_loss_f32`: Binary Cross Entropy Loss

## PyTorch Integration Patterns

### Pattern 1: Convert and Compute

```python
import torch
import hologram_ffi as hg
import json

# Create PyTorch tensors
x_torch = torch.randn(1000)

# Convert to Hologram buffers
exec_handle = hg.new_executor()
x_handle = hg.executor_allocate_buffer(exec_handle, len(x_torch))
hg.buffer_copy_from_slice(exec_handle, x_handle, json.dumps(x_torch.tolist()))

# Apply ReLU
y_handle = hg.executor_allocate_buffer(exec_handle, len(x_torch))
hg.vector_relu_f32(exec_handle, x_handle, y_handle, len(x_torch))

# Convert back to PyTorch
result_json = hg.buffer_to_vec(exec_handle, y_handle)
y_torch = torch.tensor(json.loads(result_json))

# Verify with PyTorch
y_torch_expected = torch.relu(x_torch)
print(f"Match: {torch.allclose(y_torch, y_torch_expected)}")
```

### Pattern 2: Training Loop Integration

```python
def train_step_with_hologram(model, inputs, targets, optimizer):
    """Training step using hologram for forward pass"""

    # Convert to hologram buffers
    exec_handle = hg.new_executor()

    # Flatten model inputs
    inputs_flat = inputs.flatten().tolist()
    inputs_handle = hg.executor_allocate_buffer(exec_handle, len(inputs_flat))
    hg.buffer_copy_from_slice(exec_handle, inputs_handle, json.dumps(inputs_flat))

    # Forward pass using hologram operations
    # (Apply linear transformations, activations, etc.)
    hidden_handle = hg.executor_allocate_buffer(exec_handle, 128)
    output_handle = hg.executor_allocate_buffer(exec_handle, 10)

    # For demonstration - actual implementation would use GEMM
    # hg.gemm_f32(...) for matrix multiplications

    # Compute loss
    loss_handle = hg.executor_allocate_buffer(exec_handle, 3)
    targets_flat = targets.flatten().tolist()
    targets_handle = hg.executor_allocate_buffer(exec_handle, len(targets_flat))
    hg.buffer_copy_from_slice(exec_handle, targets_handle, json.dumps(targets_flat))

    loss = hg.mse_loss_f32(exec_handle, output_handle, targets_handle, loss_handle, len(targets_flat))

    # Cleanup
    hg.buffer_cleanup(inputs_handle)
    hg.buffer_cleanup(hidden_handle)
    hg.buffer_cleanup(output_handle)
    hg.buffer_cleanup(targets_handle)
    hg.buffer_cleanup(loss_handle)
    hg.executor_cleanup(exec_handle)

    return loss
```

## Performance Considerations

### When to Use Hologram

**Use Hologram for:**

- Large batch operations (>1000 elements)
- Repeated operations in tight loops
- Operations that benefit from canonicalization
- Cache-friendly operations (fit in L2: <1.125 MiB)

**Stick with PyTorch for:**

- Small tensors (<100 elements)
- Irregular data access patterns
- Complex control flow
- Operations requiring gradients (use PyTorch's autograd)

### Memory Efficiency

- Hologram's 96-class system is designed to fit entirely in L2 cache
- Each class: 12,288 bytes (3,072 f32 elements)
- Total boundary pool: 1.125 MiB
- Operations beyond this size use linear pool with explicit management

## Example: Linear Layer

```python
def linear_layer_hologram(x: torch.Tensor, weight: torch.Tensor) -> torch.Tensor:
    """Linear layer using hologram runtime"""

    exec_handle = hg.new_executor()

    # Convert inputs
    x_np = x.flatten().tolist()
    W_np = weight.flatten().tolist()

    x_handle = hg.executor_allocate_buffer(exec_handle, len(x_np))
    W_handle = hg.executor_allocate_buffer(exec_handle, len(W_np))

    hg.buffer_copy_from_slice(exec_handle, x_handle, json.dumps(x_np))
    hg.buffer_copy_from_slice(exec_handle, W_handle, json.dumps(W_np))

    # For actual GEMM, you'd need tensor operations or manual matrix multiply
    # This is a simplified example

    # Cleanup
    hg.buffer_cleanup(x_handle)
    hg.buffer_cleanup(W_handle)
    hg.executor_cleanup(exec_handle)

    # Manual numpy for now
    x_mat = x.numpy()
    W_mat = weight.numpy()
    y_mat = np.dot(W_mat, x_mat.T).T

    return torch.from_numpy(y_mat)
```

## Running the Example

```bash
# Make sure hologram-ffi is installed
cd crates/hologram-ffi/interfaces/python
pip install -e .

# Run the example
python examples/pytorch_hologram_example.py
```

## Troubleshooting

### Import Error

If you get `ModuleNotFoundError: No module named 'hologram_ffi'`:

```bash
cd crates/hologram-ffi/interfaces/python
pip install -e .
```

### Library Not Found

If you get errors about missing `.so` files:

```bash
cd crates/hologram-ffi
cargo build --release
cp target/release/libhologram_ffi.so interfaces/python/hologram_ffi/
```

### PoisonError

If you encounter mutex poisoning errors, rebuild the library:

```bash
cd crates/hologram-ffi
cargo clean
cargo build --release
```

## Future Enhancements

- [ ] Direct tensor-to-buffer conversion without JSON serialization
- [ ] Gradient computation support
- [ ] GPU backend integration
- [ ] Automatic graph optimization
- [ ] Mixed precision support

## References

- [Hologram Architecture](../.cursor/rules/project.mdc)
- [FFI API Documentation](../crates/hologram-ffi/README.md)
- [Python Bindings](../crates/hologram-ffi/interfaces/python/README.md)
