# Hologram FFI - Python Bindings

**Python bindings for Hologram's canonical compute acceleration**

## Overview

This package provides comprehensive Python bindings for hologram-core, enabling high-performance numerical computations through canonical form compilation. The bindings expose all 50 FFI functions covering 26 core operations plus buffer, tensor, and executor management through a clean, Pythonic interface.

## Features

- **Complete Coverage**: All 50 FFI functions available (100% hologram-core coverage)
- **Canonical Compilation**: Operations compiled to minimal canonical forms via Sigmatics
- **Memory Safe**: Handle-based API with explicit resource management
- **High Performance**: Direct FFI bindings with minimal overhead
- **f32 Operations**: Optimized for neural network and ML workloads
- **Cross-Platform**: Works on Linux, macOS, and Windows
- **Comprehensive Examples**: 8 complete example files
- **Full Test Suite**: Comprehensive unit and integration tests

## Installation

### From Source

```bash
# Clone the repository
git clone <repository-url>
cd hologram-ffi/interfaces/python

# Install the package
pip install -e .
```

### Development Installation

```bash
# Install in development mode
pip install -e .[dev]

# Run tests
python -m pytest tests/

# Run examples
python examples/basic_operations.py
```

## Quick Start

```python
import hologram_ffi as hg
import json

# Get version information
print(f"Hologram FFI Version: {hg.get_version()}")

# Create an executor
executor_handle = hg.new_executor()

# Allocate buffers
size = 1024
a_handle = hg.executor_allocate_buffer(executor_handle, size)
b_handle = hg.executor_allocate_buffer(executor_handle, size)
c_handle = hg.executor_allocate_buffer(executor_handle, size)

# Fill buffers with data
data_a = [float(i) for i in range(size)]
data_b = [float(i * 2) for i in range(size)]
hg.buffer_copy_from_slice(executor_handle, a_handle, json.dumps(data_a))
hg.buffer_copy_from_slice(executor_handle, b_handle, json.dumps(data_b))

# Perform vector addition
hg.vector_add_f32(executor_handle, a_handle, b_handle, c_handle, size)

# Get results
result_json = hg.buffer_to_vec(executor_handle, c_handle)
result = json.loads(result_json)
print(f"First 10 results: {result[:10]}")

# Clean up resources
hg.buffer_cleanup(a_handle)
hg.buffer_cleanup(b_handle)
hg.buffer_cleanup(c_handle)
hg.executor_cleanup(executor_handle)
```

## API Reference

For complete API documentation, see [FFI_API_REFERENCE.md](../../../../docs/FFI_API_REFERENCE.md).

### Utility Functions (2 functions)

- `get_version()` → str - Get library version string
- `clear_all_registries()` → None - Clear all handle registries (cleanup)

### Executor Management (2 functions)

- `new_executor()` → u64 - Create new executor
- `executor_cleanup(executor_handle)` → None - Release executor

### Buffer Management (13 functions)

**Allocation:**
- `executor_allocate_buffer(executor_handle, length)` → u64 - Allocate linear buffer
- `executor_allocate_boundary_buffer(executor_handle, class, width, height)` → u64 - Allocate boundary buffer

**Properties:**
- `buffer_length(buffer_handle)` → u32 - Get buffer length
- `buffer_is_empty(buffer_handle)` → u8 - Check if empty (1=true, 0=false)
- `buffer_is_linear(buffer_handle)` → u8 - Check if in linear pool
- `buffer_is_boundary(buffer_handle)` → u8 - Check if in boundary pool
- `buffer_pool(buffer_handle)` → str - Get pool name ("Linear" or "Boundary")
- `buffer_element_size(buffer_handle)` → u32 - Get element size in bytes
- `buffer_size_bytes(buffer_handle)` → u32 - Get total size in bytes
- `buffer_class_index(buffer_handle)` → u8 - Get class index (0-95)

**Data Transfer:**
- `buffer_copy_from_slice(executor_handle, buffer_handle, data_json)` → None - Copy data from JSON array
- `buffer_to_vec(executor_handle, buffer_handle)` → str - Extract data as JSON array

**Operations:**
- `buffer_fill(executor_handle, buffer_handle, value, length)` → None - Fill with constant
- `buffer_copy(executor_handle, src_handle, dst_handle, length)` → None - Copy between buffers
- `buffer_cleanup(buffer_handle)` → None - Release buffer

### Mathematical Operations (12 functions)

**Binary Operations:**
- `vector_add_f32(executor_handle, a_handle, b_handle, c_handle, length)` → None - Element-wise addition
- `vector_sub_f32(executor_handle, a_handle, b_handle, c_handle, length)` → None - Element-wise subtraction
- `vector_mul_f32(executor_handle, a_handle, b_handle, c_handle, length)` → None - Element-wise multiplication
- `vector_div_f32(executor_handle, a_handle, b_handle, c_handle, length)` → None - Element-wise division
- `vector_min_f32(executor_handle, a_handle, b_handle, c_handle, length)` → None - Element-wise minimum
- `vector_max_f32(executor_handle, a_handle, b_handle, c_handle, length)` → None - Element-wise maximum

**Unary Operations:**
- `vector_abs_f32(executor_handle, a_handle, c_handle, length)` → None - Absolute value
- `vector_neg_f32(executor_handle, a_handle, c_handle, length)` → None - Negation
- `vector_relu_f32(executor_handle, a_handle, c_handle, length)` → None - ReLU activation

**Advanced Operations:**
- `vector_clip_f32(executor_handle, a_handle, c_handle, length, min_val, max_val)` → None - Clip to range
- `scalar_add_f32(executor_handle, a_handle, c_handle, length, scalar)` → None - Add scalar to all elements
- `scalar_mul_f32(executor_handle, a_handle, c_handle, length, scalar)` → None - Multiply all by scalar

### Reduction Operations (3 functions)

**Note:** Output buffers must have at least 3 elements for internal temporaries.

- `reduce_sum_f32(executor_handle, input_handle, output_handle, length)` → f32 - Sum all elements
- `reduce_min_f32(executor_handle, input_handle, output_handle, length)` → f32 - Find minimum
- `reduce_max_f32(executor_handle, input_handle, output_handle, length)` → f32 - Find maximum

### Activation Functions (4 functions)

- `sigmoid_f32(executor_handle, input_handle, output_handle, length)` → None - Sigmoid activation
- `tanh_f32(executor_handle, input_handle, output_handle, length)` → None - Hyperbolic tangent
- `gelu_f32(executor_handle, input_handle, output_handle, length)` → None - GELU activation
- `softmax_f32(executor_handle, input_handle, output_handle, length)` → None - Softmax activation

### Loss Functions (3 functions)

**Note:** Output buffers must have at least 3 elements for internal temporaries.

- `mse_loss_f32(executor_handle, pred_handle, target_handle, output_handle, length)` → f32 - Mean Squared Error
- `cross_entropy_loss_f32(executor_handle, pred_handle, target_handle, output_handle, length)` → f32 - Cross Entropy
- `binary_cross_entropy_loss_f32(executor_handle, pred_handle, target_handle, output_handle, length)` → f32 - Binary Cross Entropy

### Linear Algebra (2 functions)

- `gemm_f32(executor_handle, a_handle, b_handle, c_handle, m, n, k)` → None - General Matrix Multiply (C = A × B)
- `matvec_f32(executor_handle, a_handle, x_handle, y_handle, m, n)` → None - Matrix-Vector Multiply (y = A × x)

### Tensor Operations (13 functions)

**Creation:**
- `tensor_from_buffer(buffer_handle, shape_json)` → u64 - Create tensor from buffer
- `tensor_from_buffer_with_strides(buffer_handle, shape_json, strides_json)` → u64 - Create with custom strides

**Properties:**
- `tensor_shape(tensor_handle)` → str - Get shape as JSON array
- `tensor_strides(tensor_handle)` → str - Get strides as JSON array
- `tensor_offset(tensor_handle)` → u32 - Get data offset
- `tensor_ndim(tensor_handle)` → u32 - Get number of dimensions
- `tensor_numel(tensor_handle)` → u32 - Get total element count
- `tensor_is_contiguous(tensor_handle)` → u8 - Check if contiguous
- `tensor_buffer(tensor_handle)` → u64 - Get underlying buffer handle

**Operations:**
- `tensor_contiguous(executor_handle, tensor_handle)` → u64 - Create contiguous copy
- `tensor_transpose(tensor_handle)` → u64 - Transpose 2D tensor
- `tensor_reshape(executor_handle, tensor_handle, new_shape_json)` → u64 - Reshape tensor
- `tensor_select(tensor_handle, dim, index)` → u64 - Select along dimension
- `tensor_matmul(executor_handle, a_handle, b_handle)` → u64 - Matrix multiplication

**Cleanup:**
- `tensor_cleanup(tensor_handle)` → None - Release tensor (not the underlying buffer)

**Total: 50 functions**

## Usage Examples

### Vector Addition

```python
import hologram_ffi as hg
import json

# Create executor
executor = hg.new_executor()

# Allocate buffers
a = hg.executor_allocate_buffer(executor, 1024)
b = hg.executor_allocate_buffer(executor, 1024)
c = hg.executor_allocate_buffer(executor, 1024)

# Fill with data
data_a = [float(i) for i in range(1024)]
data_b = [float(i * 2) for i in range(1024)]
hg.buffer_copy_from_slice(executor, a, json.dumps(data_a))
hg.buffer_copy_from_slice(executor, b, json.dumps(data_b))

# Perform addition
hg.vector_add_f32(executor, a, b, c, 1024)

# Get results
result_json = hg.buffer_to_vec(executor, c)
result = json.loads(result_json)
print(f"First 5 results: {result[:5]}")  # [0.0, 3.0, 6.0, 9.0, 12.0]

# Cleanup
hg.buffer_cleanup(a)
hg.buffer_cleanup(b)
hg.buffer_cleanup(c)
hg.executor_cleanup(executor)
```

### Neural Network Layer

```python
import hologram_ffi as hg
import json

executor = hg.new_executor()

# Allocate buffers for 128×64 matrix and 64-element vector
size_matrix = 128 * 64
size_vec = 64
size_output = 128

matrix_buf = hg.executor_allocate_buffer(executor, size_matrix)
input_buf = hg.executor_allocate_buffer(executor, size_vec)
output_buf = hg.executor_allocate_buffer(executor, size_output)
activated_buf = hg.executor_allocate_buffer(executor, size_output)

# Fill with weights and input data...

# Linear layer: output = matrix × input
hg.matvec_f32(executor, matrix_buf, input_buf, output_buf, 128, 64)

# Apply activation: activated = sigmoid(output)
hg.sigmoid_f32(executor, output_buf, activated_buf, size_output)

# Get results
result_json = hg.buffer_to_vec(executor, activated_buf)
activations = json.loads(result_json)

# Cleanup
hg.buffer_cleanup(matrix_buf)
hg.buffer_cleanup(input_buf)
hg.buffer_cleanup(output_buf)
hg.buffer_cleanup(activated_buf)
hg.executor_cleanup(executor)
```

### Tensor Matrix Multiplication

```python
import hologram_ffi as hg
import json

executor = hg.new_executor()

# Create 4×8 and 8×3 matrices
a_buf = hg.executor_allocate_buffer(executor, 32)
b_buf = hg.executor_allocate_buffer(executor, 24)

# Create tensors
tensor_a = hg.tensor_from_buffer(a_buf, json.dumps([4, 8]))
tensor_b = hg.tensor_from_buffer(b_buf, json.dumps([8, 3]))

# Matrix multiply: result is 4×3
result_tensor = hg.tensor_matmul(executor, tensor_a, tensor_b)

# Get shape
shape_json = hg.tensor_shape(result_tensor)
shape = json.loads(shape_json)
print(f"Result shape: {shape}")  # [4, 3]

# Cleanup
hg.tensor_cleanup(result_tensor)
hg.tensor_cleanup(tensor_b)
hg.tensor_cleanup(tensor_a)
hg.buffer_cleanup(b_buf)
hg.buffer_cleanup(a_buf)
hg.executor_cleanup(executor)
```

## Error Handling

The Python bindings use Python exceptions for error handling:

```python
import hologram_ffi as hg

try:
    executor_handle = hg.new_executor()
    # ... operations ...
    hg.executor_cleanup(executor_handle)
except Exception as e:
    print(f"Error: {e}")
```

## Memory Management

All resources must be explicitly cleaned up:

```python
import hologram_ffi as hg

# Create resources
executor_handle = hg.new_executor()
buffer_handle = hg.executor_allocate_buffer(executor_handle, 1000)
tensor_handle = hg.tensor_from_buffer(buffer_handle, json.dumps([10, 100]))

# Use resources
# ... operations ...

# Clean up in reverse order
hg.tensor_cleanup(tensor_handle)
hg.buffer_cleanup(buffer_handle)
hg.executor_cleanup(executor_handle)
```

## Performance

The Python bindings provide high-performance computation through:

- **Canonical Compilation**: Operations compiled to minimal forms (typical 4-8x reduction)
- **Direct FFI**: Minimal overhead for cross-language calls
- **JSON Transfer**: Acceptable overhead for most workloads (computation >> transfer)
- **f32 Optimization**: Optimized for neural network precision requirements

**Note**: For large data transfers, minimize round-trips by batching data in single JSON arrays.

## Testing

Run the comprehensive test suite:

```bash
# Run all tests
python -m pytest tests/ -v

# Run specific test class
python -m pytest tests/test_hologram_ffi.py::TestBasicOperations -v
python -m pytest tests/test_hologram_ffi.py::TestExecutorManagement -v
python -m pytest tests/test_hologram_ffi.py::TestBufferOperations -v
python -m pytest tests/test_hologram_ffi.py::TestTensorOperations -v

# Run with coverage
python -m pytest --cov=hologram_ffi tests/
```

## Examples

The `examples/` directory contains 8 comprehensive examples:

- `basic_operations.py` - Version info and basic usage
- `simple_executor_example.py` - Simple executor workflow
- `simple_tensor_example.py` - Simple tensor operations
- `executor_management.py` - Executor and buffer management
- `buffer_operations.py` - Buffer data transfer and operations
- `tensor_operations.py` - Advanced tensor operations
- `error_handling.py` - Error handling patterns
- `performance_benchmarks.py` - Performance measurements

Run examples:

```bash
python examples/simple_executor_example.py
python examples/tensor_operations.py
python examples/performance_benchmarks.py
```

## Contributing

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests for new functionality
5. Run the test suite
6. Submit a pull request

## License

This project is licensed under the same license as the main hologram-ffi project.

## Support

For questions, issues, or contributions:

- Create an issue on GitHub
- Check the examples for usage patterns
- Review the test suite for implementation details
