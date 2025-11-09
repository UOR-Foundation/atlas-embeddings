# Hologram FFI API Reference

**Version:** 1.0.0
**Last Updated:** 2025-10-30
**Status:** Production Ready

This document provides a comprehensive reference for all 50 functions exposed by the hologram-ffi library.

## Table of Contents

1. [Overview](#overview)
2. [Executor Management](#executor-management)
3. [Buffer Management](#buffer-management)
4. [Mathematical Operations](#mathematical-operations)
5. [Reduction Operations](#reduction-operations)
6. [Activation Functions](#activation-functions)
7. [Loss Functions](#loss-functions)
8. [Linear Algebra](#linear-algebra)
9. [Tensor Operations](#tensor-operations)
10. [Utility Functions](#utility-functions)
11. [Type Reference](#type-reference)
12. [Error Handling](#error-handling)

---

## Overview

The Hologram FFI provides cross-language bindings to hologram-core's canonical compute acceleration capabilities. All operations use handle-based access for memory safety across language boundaries.

### Key Concepts

- **Handles**: Opaque u64 identifiers for executors, buffers, and tensors
- **JSON Serialization**: Data transfer uses JSON for type safety and cross-platform compatibility
- **f32 Operations**: All operations currently support 32-bit floating point (f32) only
- **Thread Safety**: Global registries use RwLock for safe concurrent access

### Handle Lifecycle

```
1. Create → Returns handle (u64)
2. Use → Pass handle to functions
3. Cleanup → Call appropriate cleanup function
```

**Important**: Always call cleanup functions to prevent memory leaks.

---

## Executor Management

Executors manage backend execution and buffer allocation.

### `new_executor`

Creates a new executor instance.

**Signature:**
```rust
fn new_executor() -> u64
```

**Returns:**
- Handle to the new executor (u64)

**Example (Python):**
```python
import hologram_ffi as hg

executor_handle = hg.new_executor()
# Use executor...
hg.executor_cleanup(executor_handle)
```

**Example (TypeScript):**
```typescript
import * as hg from 'hologram-ffi';

const executorHandle = hg.new_executor();
// Use executor...
hg.executor_cleanup(executorHandle);
```

---

### `executor_cleanup`

Releases an executor and its associated resources.

**Signature:**
```rust
fn executor_cleanup(executor_handle: u64)
```

**Parameters:**
- `executor_handle`: Handle to executor to release

**Example (Python):**
```python
hg.executor_cleanup(executor_handle)
```

---

### `executor_allocate_buffer`

Allocates a buffer in the linear memory pool.

**Signature:**
```rust
fn executor_allocate_buffer(executor_handle: u64, len: u32) -> u64
```

**Parameters:**
- `executor_handle`: Executor handle
- `len`: Number of elements to allocate

**Returns:**
- Handle to the allocated buffer (u64)

**Example (Python):**
```python
# Allocate buffer for 1024 f32 elements
buffer_handle = hg.executor_allocate_buffer(executor_handle, 1024)
```

---

### `executor_allocate_boundary_buffer`

Allocates a buffer in the boundary-specific memory pool using Φ-coordinate addressing.

**Signature:**
```rust
fn executor_allocate_boundary_buffer(
    executor_handle: u64,
    class: u8,
    width: u32,
    height: u32
) -> u64
```

**Parameters:**
- `executor_handle`: Executor handle
- `class`: Class index (0-95) for geometric addressing
- `width`: Buffer width dimension
- `height`: Buffer height dimension

**Returns:**
- Handle to the allocated boundary buffer (u64)

**Example (Python):**
```python
# Allocate 32x32 boundary buffer in class 0
boundary_buf = hg.executor_allocate_boundary_buffer(executor_handle, 0, 32, 32)
```

---

## Buffer Management

Buffer management functions provide introspection and data transfer capabilities.

### `buffer_length`

Gets the number of elements in a buffer.

**Signature:**
```rust
fn buffer_length(buffer_handle: u64) -> u32
```

**Parameters:**
- `buffer_handle`: Buffer handle

**Returns:**
- Number of elements (u32)

**Example (Python):**
```python
length = hg.buffer_length(buffer_handle)
print(f"Buffer has {length} elements")
```

---

### `buffer_is_empty`

Checks if a buffer is empty.

**Signature:**
```rust
fn buffer_is_empty(buffer_handle: u64) -> u8
```

**Parameters:**
- `buffer_handle`: Buffer handle

**Returns:**
- 1 if empty, 0 if not empty (u8 as boolean)

**Example (Python):**
```python
if hg.buffer_is_empty(buffer_handle):
    print("Buffer is empty")
```

---

### `buffer_is_linear`

Checks if a buffer is in the linear memory pool.

**Signature:**
```rust
fn buffer_is_linear(buffer_handle: u64) -> u8
```

**Parameters:**
- `buffer_handle`: Buffer handle

**Returns:**
- 1 if in linear pool, 0 otherwise (u8 as boolean)

**Example (Python):**
```python
if hg.buffer_is_linear(buffer_handle):
    print("Buffer is in linear pool")
```

---

### `buffer_is_boundary`

Checks if a buffer is in the boundary memory pool.

**Signature:**
```rust
fn buffer_is_boundary(buffer_handle: u64) -> u8
```

**Parameters:**
- `buffer_handle`: Buffer handle

**Returns:**
- 1 if in boundary pool, 0 otherwise (u8 as boolean)

**Example (Python):**
```python
if hg.buffer_is_boundary(buffer_handle):
    print("Buffer is in boundary pool")
```

---

### `buffer_pool`

Gets the name of the memory pool containing the buffer.

**Signature:**
```rust
fn buffer_pool(buffer_handle: u64) -> String
```

**Parameters:**
- `buffer_handle`: Buffer handle

**Returns:**
- Pool name as string ("Linear" or "Boundary")

**Example (Python):**
```python
pool_name = hg.buffer_pool(buffer_handle)
print(f"Buffer is in {pool_name} pool")
```

---

### `buffer_element_size`

Gets the size of each element in bytes.

**Signature:**
```rust
fn buffer_element_size(buffer_handle: u64) -> u32
```

**Parameters:**
- `buffer_handle`: Buffer handle

**Returns:**
- Element size in bytes (u32)

**Example (Python):**
```python
elem_size = hg.buffer_element_size(buffer_handle)
print(f"Each element is {elem_size} bytes")  # f32 = 4 bytes
```

---

### `buffer_size_bytes`

Gets the total buffer size in bytes.

**Signature:**
```rust
fn buffer_size_bytes(buffer_handle: u64) -> u32
```

**Parameters:**
- `buffer_handle`: Buffer handle

**Returns:**
- Total size in bytes (u32)

**Example (Python):**
```python
total_bytes = hg.buffer_size_bytes(buffer_handle)
print(f"Buffer occupies {total_bytes} bytes")
```

---

### `buffer_class_index`

Gets the class index for boundary buffers.

**Signature:**
```rust
fn buffer_class_index(buffer_handle: u64) -> u8
```

**Parameters:**
- `buffer_handle`: Buffer handle

**Returns:**
- Class index (0-95) for boundary buffers, or 0 for linear buffers

**Example (Python):**
```python
class_idx = hg.buffer_class_index(buffer_handle)
print(f"Buffer is in class {class_idx}")
```

---

### `buffer_copy_from_slice`

Copies data into a buffer from JSON-encoded array.

**Signature:**
```rust
fn buffer_copy_from_slice(
    executor_handle: u64,
    buffer_handle: u64,
    data_json: String
)
```

**Parameters:**
- `executor_handle`: Executor handle
- `buffer_handle`: Target buffer handle
- `data_json`: JSON-encoded array of f32 values

**Example (Python):**
```python
import json

data = [1.0, 2.0, 3.0, 4.0]
data_json = json.dumps(data)
hg.buffer_copy_from_slice(executor_handle, buffer_handle, data_json)
```

---

### `buffer_to_vec`

Extracts buffer data as JSON-encoded array.

**Signature:**
```rust
fn buffer_to_vec(executor_handle: u64, buffer_handle: u64) -> String
```

**Parameters:**
- `executor_handle`: Executor handle
- `buffer_handle`: Source buffer handle

**Returns:**
- JSON-encoded array of f32 values (String)

**Example (Python):**
```python
import json

data_json = hg.buffer_to_vec(executor_handle, buffer_handle)
data = json.loads(data_json)
print(f"Buffer contains: {data}")
```

---

### `buffer_fill`

Fills a buffer with a constant value.

**Signature:**
```rust
fn buffer_fill(
    executor_handle: u64,
    buffer_handle: u64,
    value: f32,
    len: u32
)
```

**Parameters:**
- `executor_handle`: Executor handle
- `buffer_handle`: Target buffer handle
- `value`: Value to fill with (f32)
- `len`: Number of elements to fill

**Example (Python):**
```python
# Fill buffer with zeros
hg.buffer_fill(executor_handle, buffer_handle, 0.0, 1024)
```

---

### `buffer_copy`

Copies data from one buffer to another.

**Signature:**
```rust
fn buffer_copy(
    executor_handle: u64,
    src_handle: u64,
    dst_handle: u64,
    len: u32
)
```

**Parameters:**
- `executor_handle`: Executor handle
- `src_handle`: Source buffer handle
- `dst_handle`: Destination buffer handle
- `len`: Number of elements to copy

**Example (Python):**
```python
# Copy 512 elements from src to dst
hg.buffer_copy(executor_handle, src_handle, dst_handle, 512)
```

---

### `buffer_cleanup`

Releases a buffer and its associated resources.

**Signature:**
```rust
fn buffer_cleanup(buffer_handle: u64)
```

**Parameters:**
- `buffer_handle`: Handle to buffer to release

**Example (Python):**
```python
hg.buffer_cleanup(buffer_handle)
```

---

## Mathematical Operations

All mathematical operations are element-wise and operate on f32 buffers.

### `vector_add_f32`

Element-wise addition: `c[i] = a[i] + b[i]`

**Signature:**
```rust
fn vector_add_f32(
    executor_handle: u64,
    a_handle: u64,
    b_handle: u64,
    c_handle: u64,
    len: u32
)
```

**Parameters:**
- `executor_handle`: Executor handle
- `a_handle`: First input buffer
- `b_handle`: Second input buffer
- `c_handle`: Output buffer
- `len`: Number of elements

**Example (Python):**
```python
# c = a + b
hg.vector_add_f32(executor_handle, a_handle, b_handle, c_handle, 1024)
```

---

### `vector_sub_f32`

Element-wise subtraction: `c[i] = a[i] - b[i]`

**Signature:**
```rust
fn vector_sub_f32(
    executor_handle: u64,
    a_handle: u64,
    b_handle: u64,
    c_handle: u64,
    len: u32
)
```

**Parameters:**
- `executor_handle`: Executor handle
- `a_handle`: First input buffer
- `b_handle`: Second input buffer
- `c_handle`: Output buffer
- `len`: Number of elements

**Example (Python):**
```python
# c = a - b
hg.vector_sub_f32(executor_handle, a_handle, b_handle, c_handle, 1024)
```

---

### `vector_mul_f32`

Element-wise multiplication: `c[i] = a[i] * b[i]`

**Signature:**
```rust
fn vector_mul_f32(
    executor_handle: u64,
    a_handle: u64,
    b_handle: u64,
    c_handle: u64,
    len: u32
)
```

**Parameters:**
- `executor_handle`: Executor handle
- `a_handle`: First input buffer
- `b_handle`: Second input buffer
- `c_handle`: Output buffer
- `len`: Number of elements

**Example (Python):**
```python
# c = a * b (element-wise)
hg.vector_mul_f32(executor_handle, a_handle, b_handle, c_handle, 1024)
```

---

### `vector_div_f32`

Element-wise division: `c[i] = a[i] / b[i]`

**Signature:**
```rust
fn vector_div_f32(
    executor_handle: u64,
    a_handle: u64,
    b_handle: u64,
    c_handle: u64,
    len: u32
)
```

**Parameters:**
- `executor_handle`: Executor handle
- `a_handle`: Numerator buffer
- `b_handle`: Denominator buffer
- `c_handle`: Output buffer
- `len`: Number of elements

**Example (Python):**
```python
# c = a / b (element-wise)
hg.vector_div_f32(executor_handle, a_handle, b_handle, c_handle, 1024)
```

---

### `vector_min_f32`

Element-wise minimum: `c[i] = min(a[i], b[i])`

**Signature:**
```rust
fn vector_min_f32(
    executor_handle: u64,
    a_handle: u64,
    b_handle: u64,
    c_handle: u64,
    len: u32
)
```

**Parameters:**
- `executor_handle`: Executor handle
- `a_handle`: First input buffer
- `b_handle`: Second input buffer
- `c_handle`: Output buffer
- `len`: Number of elements

**Example (Python):**
```python
# c[i] = min(a[i], b[i])
hg.vector_min_f32(executor_handle, a_handle, b_handle, c_handle, 1024)
```

---

### `vector_max_f32`

Element-wise maximum: `c[i] = max(a[i], b[i])`

**Signature:**
```rust
fn vector_max_f32(
    executor_handle: u64,
    a_handle: u64,
    b_handle: u64,
    c_handle: u64,
    len: u32
)
```

**Parameters:**
- `executor_handle`: Executor handle
- `a_handle`: First input buffer
- `b_handle`: Second input buffer
- `c_handle`: Output buffer
- `len`: Number of elements

**Example (Python):**
```python
# c[i] = max(a[i], b[i])
hg.vector_max_f32(executor_handle, a_handle, b_handle, c_handle, 1024)
```

---

### `vector_abs_f32`

Element-wise absolute value: `c[i] = |a[i]|`

**Signature:**
```rust
fn vector_abs_f32(
    executor_handle: u64,
    a_handle: u64,
    c_handle: u64,
    len: u32
)
```

**Parameters:**
- `executor_handle`: Executor handle
- `a_handle`: Input buffer
- `c_handle`: Output buffer
- `len`: Number of elements

**Example (Python):**
```python
# c = |a|
hg.vector_abs_f32(executor_handle, a_handle, c_handle, 1024)
```

---

### `vector_neg_f32`

Element-wise negation: `c[i] = -a[i]`

**Signature:**
```rust
fn vector_neg_f32(
    executor_handle: u64,
    a_handle: u64,
    c_handle: u64,
    len: u32
)
```

**Parameters:**
- `executor_handle`: Executor handle
- `a_handle`: Input buffer
- `c_handle`: Output buffer
- `len`: Number of elements

**Example (Python):**
```python
# c = -a
hg.vector_neg_f32(executor_handle, a_handle, c_handle, 1024)
```

---

### `vector_relu_f32`

Element-wise ReLU activation: `c[i] = max(0, a[i])`

**Signature:**
```rust
fn vector_relu_f32(
    executor_handle: u64,
    a_handle: u64,
    c_handle: u64,
    len: u32
)
```

**Parameters:**
- `executor_handle`: Executor handle
- `a_handle`: Input buffer
- `c_handle`: Output buffer
- `len`: Number of elements

**Example (Python):**
```python
# c[i] = max(0, a[i])
hg.vector_relu_f32(executor_handle, a_handle, c_handle, 1024)
```

---

### `vector_clip_f32`

Element-wise clipping: `c[i] = clamp(a[i], min_val, max_val)`

**Signature:**
```rust
fn vector_clip_f32(
    executor_handle: u64,
    a_handle: u64,
    c_handle: u64,
    len: u32,
    min_val: f32,
    max_val: f32
)
```

**Parameters:**
- `executor_handle`: Executor handle
- `a_handle`: Input buffer
- `c_handle`: Output buffer
- `len`: Number of elements
- `min_val`: Minimum value
- `max_val`: Maximum value

**Example (Python):**
```python
# Clip values to [-1.0, 1.0]
hg.vector_clip_f32(executor_handle, a_handle, c_handle, 1024, -1.0, 1.0)
```

---

### `scalar_add_f32`

Add scalar to all elements: `c[i] = a[i] + scalar`

**Signature:**
```rust
fn scalar_add_f32(
    executor_handle: u64,
    a_handle: u64,
    c_handle: u64,
    len: u32,
    scalar: f32
)
```

**Parameters:**
- `executor_handle`: Executor handle
- `a_handle`: Input buffer
- `c_handle`: Output buffer
- `len`: Number of elements
- `scalar`: Scalar value to add

**Example (Python):**
```python
# Add 5.0 to all elements
hg.scalar_add_f32(executor_handle, a_handle, c_handle, 1024, 5.0)
```

---

### `scalar_mul_f32`

Multiply all elements by scalar: `c[i] = a[i] * scalar`

**Signature:**
```rust
fn scalar_mul_f32(
    executor_handle: u64,
    a_handle: u64,
    c_handle: u64,
    len: u32,
    scalar: f32
)
```

**Parameters:**
- `executor_handle`: Executor handle
- `a_handle`: Input buffer
- `c_handle`: Output buffer
- `len`: Number of elements
- `scalar`: Scalar multiplier

**Example (Python):**
```python
# Multiply all elements by 2.0
hg.scalar_mul_f32(executor_handle, a_handle, c_handle, 1024, 2.0)
```

---

## Reduction Operations

Reduction operations collapse a buffer to a single value. **Important**: Output buffers must have at least 3 elements for internal temporaries. The result is stored in the first element and also returned directly.

### `reduce_sum_f32`

Computes the sum of all elements.

**Signature:**
```rust
fn reduce_sum_f32(
    executor_handle: u64,
    input_handle: u64,
    output_handle: u64,
    len: u32
) -> f32
```

**Parameters:**
- `executor_handle`: Executor handle
- `input_handle`: Input buffer
- `output_handle`: Output buffer (must have ≥3 elements)
- `len`: Number of elements to reduce

**Returns:**
- Sum of all elements (f32)

**Example (Python):**
```python
# Output buffer needs at least 3 elements
output_buf = hg.executor_allocate_buffer(executor_handle, 3)
sum_value = hg.reduce_sum_f32(executor_handle, input_handle, output_buf, 1024)
print(f"Sum: {sum_value}")
```

---

### `reduce_min_f32`

Finds the minimum value.

**Signature:**
```rust
fn reduce_min_f32(
    executor_handle: u64,
    input_handle: u64,
    output_handle: u64,
    len: u32
) -> f32
```

**Parameters:**
- `executor_handle`: Executor handle
- `input_handle`: Input buffer
- `output_handle`: Output buffer (must have ≥3 elements)
- `len`: Number of elements to reduce

**Returns:**
- Minimum value (f32)

**Example (Python):**
```python
output_buf = hg.executor_allocate_buffer(executor_handle, 3)
min_value = hg.reduce_min_f32(executor_handle, input_handle, output_buf, 1024)
print(f"Min: {min_value}")
```

---

### `reduce_max_f32`

Finds the maximum value.

**Signature:**
```rust
fn reduce_max_f32(
    executor_handle: u64,
    input_handle: u64,
    output_handle: u64,
    len: u32
) -> f32
```

**Parameters:**
- `executor_handle`: Executor handle
- `input_handle`: Input buffer
- `output_handle`: Output buffer (must have ≥3 elements)
- `len`: Number of elements to reduce

**Returns:**
- Maximum value (f32)

**Example (Python):**
```python
output_buf = hg.executor_allocate_buffer(executor_handle, 3)
max_value = hg.reduce_max_f32(executor_handle, input_handle, output_buf, 1024)
print(f"Max: {max_value}")
```

---

## Activation Functions

Activation functions commonly used in neural networks.

### `sigmoid_f32`

Applies sigmoid activation: `output[i] = 1 / (1 + e^(-input[i]))`

**Signature:**
```rust
fn sigmoid_f32(
    executor_handle: u64,
    input_handle: u64,
    output_handle: u64,
    len: u32
)
```

**Parameters:**
- `executor_handle`: Executor handle
- `input_handle`: Input buffer
- `output_handle`: Output buffer
- `len`: Number of elements

**Example (Python):**
```python
hg.sigmoid_f32(executor_handle, input_handle, output_handle, 1024)
```

---

### `tanh_f32`

Applies hyperbolic tangent activation: `output[i] = tanh(input[i])`

**Signature:**
```rust
fn tanh_f32(
    executor_handle: u64,
    input_handle: u64,
    output_handle: u64,
    len: u32
)
```

**Parameters:**
- `executor_handle`: Executor handle
- `input_handle`: Input buffer
- `output_handle`: Output buffer
- `len`: Number of elements

**Example (Python):**
```python
hg.tanh_f32(executor_handle, input_handle, output_handle, 1024)
```

---

### `gelu_f32`

Applies GELU (Gaussian Error Linear Unit) activation.

**Signature:**
```rust
fn gelu_f32(
    executor_handle: u64,
    input_handle: u64,
    output_handle: u64,
    len: u32
)
```

**Parameters:**
- `executor_handle`: Executor handle
- `input_handle`: Input buffer
- `output_handle`: Output buffer
- `len`: Number of elements

**Example (Python):**
```python
hg.gelu_f32(executor_handle, input_handle, output_handle, 1024)
```

---

### `softmax_f32`

Applies softmax activation: `output[i] = e^input[i] / sum(e^input[j])`

**Signature:**
```rust
fn softmax_f32(
    executor_handle: u64,
    input_handle: u64,
    output_handle: u64,
    len: u32
)
```

**Parameters:**
- `executor_handle`: Executor handle
- `input_handle`: Input buffer
- `output_handle`: Output buffer
- `len`: Number of elements

**Example (Python):**
```python
hg.softmax_f32(executor_handle, input_handle, output_handle, 1024)
```

---

## Loss Functions

Loss functions for neural network training. **Important**: Output buffers must have at least 3 elements for internal temporaries.

### `mse_loss_f32`

Computes Mean Squared Error: `MSE = (1/n) * Σ(predictions[i] - targets[i])²`

**Signature:**
```rust
fn mse_loss_f32(
    executor_handle: u64,
    pred_handle: u64,
    target_handle: u64,
    output_handle: u64,
    len: u32
) -> f32
```

**Parameters:**
- `executor_handle`: Executor handle
- `pred_handle`: Predictions buffer
- `target_handle`: Targets buffer
- `output_handle`: Output buffer (must have ≥3 elements)
- `len`: Number of elements

**Returns:**
- Mean squared error (f32)

**Example (Python):**
```python
output_buf = hg.executor_allocate_buffer(executor_handle, 3)
mse = hg.mse_loss_f32(executor_handle, pred_handle, target_handle, output_buf, 1024)
print(f"MSE Loss: {mse}")
```

---

### `cross_entropy_loss_f32`

Computes Cross Entropy Loss: `-Σ(targets[i] * log(predictions[i]))`

**Signature:**
```rust
fn cross_entropy_loss_f32(
    executor_handle: u64,
    pred_handle: u64,
    target_handle: u64,
    output_handle: u64,
    len: u32
) -> f32
```

**Parameters:**
- `executor_handle`: Executor handle
- `pred_handle`: Predictions buffer (probabilities)
- `target_handle`: Targets buffer
- `output_handle`: Output buffer (must have ≥3 elements)
- `len`: Number of elements

**Returns:**
- Cross entropy loss (f32)

**Example (Python):**
```python
output_buf = hg.executor_allocate_buffer(executor_handle, 3)
ce_loss = hg.cross_entropy_loss_f32(executor_handle, pred_handle, target_handle, output_buf, 1024)
print(f"Cross Entropy Loss: {ce_loss}")
```

---

### `binary_cross_entropy_loss_f32`

Computes Binary Cross Entropy Loss for binary classification.

**Signature:**
```rust
fn binary_cross_entropy_loss_f32(
    executor_handle: u64,
    pred_handle: u64,
    target_handle: u64,
    output_handle: u64,
    len: u32
) -> f32
```

**Parameters:**
- `executor_handle`: Executor handle
- `pred_handle`: Predictions buffer (probabilities 0-1)
- `target_handle`: Targets buffer (0 or 1)
- `output_handle`: Output buffer (must have ≥3 elements)
- `len`: Number of elements

**Returns:**
- Binary cross entropy loss (f32)

**Example (Python):**
```python
output_buf = hg.executor_allocate_buffer(executor_handle, 3)
bce_loss = hg.binary_cross_entropy_loss_f32(executor_handle, pred_handle, target_handle, output_buf, 1024)
print(f"Binary Cross Entropy Loss: {bce_loss}")
```

---

## Linear Algebra

High-performance linear algebra operations.

### `gemm_f32`

General Matrix Multiplication: `C = A × B`

**Signature:**
```rust
fn gemm_f32(
    executor_handle: u64,
    a_handle: u64,
    b_handle: u64,
    c_handle: u64,
    m: u32,
    n: u32,
    k: u32
)
```

**Parameters:**
- `executor_handle`: Executor handle
- `a_handle`: Matrix A buffer (m×k, row-major)
- `b_handle`: Matrix B buffer (k×n, row-major)
- `c_handle`: Matrix C buffer (m×n, row-major)
- `m`: Number of rows in A and C
- `n`: Number of columns in B and C
- `k`: Number of columns in A and rows in B

**Matrix Dimensions:**
- A: `m × k`
- B: `k × n`
- C: `m × n`

**Example (Python):**
```python
# Multiply 64×128 matrix by 128×32 matrix → 64×32 result
m, k, n = 64, 128, 32

a_buf = hg.executor_allocate_buffer(executor_handle, m * k)
b_buf = hg.executor_allocate_buffer(executor_handle, k * n)
c_buf = hg.executor_allocate_buffer(executor_handle, m * n)

# Fill matrices with data...

hg.gemm_f32(executor_handle, a_buf, b_buf, c_buf, m, n, k)
```

---

### `matvec_f32`

Matrix-Vector Multiplication: `y = A × x`

**Signature:**
```rust
fn matvec_f32(
    executor_handle: u64,
    a_handle: u64,
    x_handle: u64,
    y_handle: u64,
    m: u32,
    n: u32
)
```

**Parameters:**
- `executor_handle`: Executor handle
- `a_handle`: Matrix A buffer (m×n, row-major)
- `x_handle`: Vector x buffer (n elements)
- `y_handle`: Vector y buffer (m elements)
- `m`: Number of rows in A
- `n`: Number of columns in A

**Dimensions:**
- A: `m × n`
- x: `n` elements
- y: `m` elements

**Example (Python):**
```python
# Multiply 128×64 matrix by 64-element vector → 128-element result
m, n = 128, 64

a_buf = hg.executor_allocate_buffer(executor_handle, m * n)
x_buf = hg.executor_allocate_buffer(executor_handle, n)
y_buf = hg.executor_allocate_buffer(executor_handle, m)

# Fill matrix and vector with data...

hg.matvec_f32(executor_handle, a_buf, x_buf, y_buf, m, n)
```

---

## Tensor Operations

Multi-dimensional tensor operations with shape and stride management.

### `tensor_from_buffer`

Creates a tensor from a buffer with specified shape.

**Signature:**
```rust
fn tensor_from_buffer(buffer_handle: u64, shape_json: String) -> u64
```

**Parameters:**
- `buffer_handle`: Buffer handle containing data
- `shape_json`: JSON array of dimension sizes

**Returns:**
- Tensor handle (u64)

**Example (Python):**
```python
import json

# Create 4×8 tensor
shape = [4, 8]
tensor_handle = hg.tensor_from_buffer(buffer_handle, json.dumps(shape))
```

---

### `tensor_from_buffer_with_strides`

Creates a tensor with custom strides.

**Signature:**
```rust
fn tensor_from_buffer_with_strides(
    buffer_handle: u64,
    shape_json: String,
    strides_json: String
) -> u64
```

**Parameters:**
- `buffer_handle`: Buffer handle
- `shape_json`: JSON array of dimension sizes
- `strides_json`: JSON array of stride values

**Returns:**
- Tensor handle (u64)

**Example (Python):**
```python
import json

shape = [4, 8]
strides = [8, 1]  # Row-major layout
tensor_handle = hg.tensor_from_buffer_with_strides(
    buffer_handle,
    json.dumps(shape),
    json.dumps(strides)
)
```

---

### `tensor_shape`

Gets the shape of a tensor.

**Signature:**
```rust
fn tensor_shape(tensor_handle: u64) -> String
```

**Parameters:**
- `tensor_handle`: Tensor handle

**Returns:**
- JSON array of dimension sizes

**Example (Python):**
```python
import json

shape_json = hg.tensor_shape(tensor_handle)
shape = json.loads(shape_json)
print(f"Tensor shape: {shape}")
```

---

### `tensor_strides`

Gets the strides of a tensor.

**Signature:**
```rust
fn tensor_strides(tensor_handle: u64) -> String
```

**Parameters:**
- `tensor_handle`: Tensor handle

**Returns:**
- JSON array of stride values

**Example (Python):**
```python
import json

strides_json = hg.tensor_strides(tensor_handle)
strides = json.loads(strides_json)
print(f"Tensor strides: {strides}")
```

---

### `tensor_offset`

Gets the data offset of a tensor.

**Signature:**
```rust
fn tensor_offset(tensor_handle: u64) -> u32
```

**Parameters:**
- `tensor_handle`: Tensor handle

**Returns:**
- Offset in elements (u32)

---

### `tensor_ndim`

Gets the number of dimensions.

**Signature:**
```rust
fn tensor_ndim(tensor_handle: u64) -> u32
```

**Parameters:**
- `tensor_handle`: Tensor handle

**Returns:**
- Number of dimensions (u32)

**Example (Python):**
```python
ndim = hg.tensor_ndim(tensor_handle)
print(f"Tensor has {ndim} dimensions")
```

---

### `tensor_numel`

Gets the total number of elements.

**Signature:**
```rust
fn tensor_numel(tensor_handle: u64) -> u32
```

**Parameters:**
- `tensor_handle`: Tensor handle

**Returns:**
- Total number of elements (u32)

**Example (Python):**
```python
numel = hg.tensor_numel(tensor_handle)
print(f"Tensor has {numel} elements")
```

---

### `tensor_is_contiguous`

Checks if tensor data is contiguous in memory.

**Signature:**
```rust
fn tensor_is_contiguous(tensor_handle: u64) -> u8
```

**Parameters:**
- `tensor_handle`: Tensor handle

**Returns:**
- 1 if contiguous, 0 otherwise (u8 as boolean)

**Example (Python):**
```python
if hg.tensor_is_contiguous(tensor_handle):
    print("Tensor is contiguous")
```

---

### `tensor_contiguous`

Creates a contiguous copy of a tensor.

**Signature:**
```rust
fn tensor_contiguous(executor_handle: u64, tensor_handle: u64) -> u64
```

**Parameters:**
- `executor_handle`: Executor handle
- `tensor_handle`: Source tensor handle

**Returns:**
- New contiguous tensor handle (u64)

**Example (Python):**
```python
contiguous_tensor = hg.tensor_contiguous(executor_handle, tensor_handle)
```

---

### `tensor_transpose`

Transposes a 2D tensor.

**Signature:**
```rust
fn tensor_transpose(tensor_handle: u64) -> u64
```

**Parameters:**
- `tensor_handle`: Tensor handle (must be 2D)

**Returns:**
- Transposed tensor handle (u64)

**Example (Python):**
```python
# Transpose 4×8 tensor → 8×4 tensor
transposed = hg.tensor_transpose(tensor_handle)
```

---

### `tensor_reshape`

Reshapes a tensor to new dimensions.

**Signature:**
```rust
fn tensor_reshape(
    executor_handle: u64,
    tensor_handle: u64,
    new_shape_json: String
) -> u64
```

**Parameters:**
- `executor_handle`: Executor handle
- `tensor_handle`: Source tensor handle
- `new_shape_json`: JSON array of new dimension sizes

**Returns:**
- Reshaped tensor handle (u64)

**Example (Python):**
```python
import json

# Reshape 32-element tensor to 4×8
new_shape = [4, 8]
reshaped = hg.tensor_reshape(executor_handle, tensor_handle, json.dumps(new_shape))
```

---

### `tensor_select`

Selects an index along a dimension.

**Signature:**
```rust
fn tensor_select(tensor_handle: u64, dim: u32, index: u32) -> u64
```

**Parameters:**
- `tensor_handle`: Tensor handle
- `dim`: Dimension to select from
- `index`: Index to select

**Returns:**
- New tensor with one fewer dimension (u64)

**Example (Python):**
```python
# Select row 2 from 4×8 tensor → 8-element tensor
row = hg.tensor_select(tensor_handle, 0, 2)
```

---

### `tensor_matmul`

Matrix multiplication for 2D tensors.

**Signature:**
```rust
fn tensor_matmul(
    executor_handle: u64,
    a_handle: u64,
    b_handle: u64
) -> u64
```

**Parameters:**
- `executor_handle`: Executor handle
- `a_handle`: First tensor (m×k)
- `b_handle`: Second tensor (k×n)

**Returns:**
- Result tensor (m×n) handle (u64)

**Example (Python):**
```python
# Multiply 4×8 tensor by 8×3 tensor → 4×3 result
result = hg.tensor_matmul(executor_handle, a_handle, b_handle)
```

---

### `tensor_buffer`

Gets the underlying buffer handle of a tensor.

**Signature:**
```rust
fn tensor_buffer(tensor_handle: u64) -> u64
```

**Parameters:**
- `tensor_handle`: Tensor handle

**Returns:**
- Buffer handle (u64)

**Example (Python):**
```python
buffer_handle = hg.tensor_buffer(tensor_handle)
```

---

### `tensor_cleanup`

Releases a tensor (but not the underlying buffer).

**Signature:**
```rust
fn tensor_cleanup(tensor_handle: u64)
```

**Parameters:**
- `tensor_handle`: Tensor handle to release

**Example (Python):**
```python
hg.tensor_cleanup(tensor_handle)
```

---

## Utility Functions

### `get_version`

Gets the library version string.

**Signature:**
```rust
fn get_version() -> String
```

**Returns:**
- Version string (e.g., "1.0.0")

**Example (Python):**
```python
version = hg.get_version()
print(f"Hologram FFI version: {version}")
```

---

### `clear_all_registries`

Clears all global handle registries. Use for cleanup or testing.

**Signature:**
```rust
fn clear_all_registries()
```

**Warning**: This will invalidate all existing handles. Only use when you're done with all operations.

**Example (Python):**
```python
# Clean up everything
hg.clear_all_registries()
```

---

## Type Reference

### Handle Types

All handles are opaque `u64` identifiers:

- **ExecutorHandle**: Identifies an executor instance
- **BufferHandle**: Identifies a buffer in memory
- **TensorHandle**: Identifies a tensor view

### Primitive Types

- **u8**: Unsigned 8-bit integer (used for boolean returns: 1=true, 0=false)
- **u32**: Unsigned 32-bit integer (used for sizes, dimensions, indices)
- **u64**: Unsigned 64-bit integer (used for handles)
- **f32**: 32-bit floating point (all numeric operations)

### JSON Encoding

Data transfer uses JSON for arrays:

```python
# Python example
import json

# Encoding data to JSON
data = [1.0, 2.0, 3.0, 4.0]
json_str = json.dumps(data)

# Decoding data from JSON
json_str = hg.buffer_to_vec(executor_handle, buffer_handle)
data = json.loads(json_str)
```

```typescript
// TypeScript example

// Encoding data to JSON
const data = [1.0, 2.0, 3.0, 4.0];
const jsonStr = JSON.stringify(data);

// Decoding data from JSON
const jsonStr = hg.buffer_to_vec(executorHandle, bufferHandle);
const data = JSON.parse(jsonStr);
```

---

## Error Handling

The FFI uses panics for error handling. In language bindings, these manifest as:

**Python:**
```python
try:
    result = hg.vector_add_f32(exec_handle, a_handle, b_handle, c_handle, 1024)
except Exception as e:
    print(f"Operation failed: {e}")
```

**TypeScript:**
```typescript
try {
    hg.vector_add_f32(execHandle, aHandle, bHandle, cHandle, 1024);
} catch (error) {
    console.error('Operation failed:', error);
}
```

### Common Error Scenarios

1. **Invalid Handle**: Using a handle that doesn't exist or has been cleaned up
2. **Dimension Mismatch**: Buffer/tensor size doesn't match operation requirements
3. **Memory Allocation Failure**: System out of memory
4. **Invalid Arguments**: Negative sizes, null pointers, invalid class indices

### Best Practices

1. **Always cleanup resources**: Call cleanup functions when done
2. **Check buffer sizes**: Ensure buffers are large enough for operations
3. **Validate dimensions**: Verify tensor/matrix dimensions before linalg ops
4. **Handle exceptions**: Wrap FFI calls in try-catch blocks
5. **Use correct output sizes**: Remember reductions need 3-element output buffers

---

## Performance Considerations

### JSON Serialization Overhead

Buffer data transfer uses JSON encoding, which adds overhead:

```python
# For large transfers, minimize round-trips
# ❌ Bad: Multiple small transfers
for i in range(1000):
    data = [float(i)]
    hg.buffer_copy_from_slice(exec, buf, json.dumps(data))

# ✅ Good: Single large transfer
data = [float(i) for i in range(1000)]
hg.buffer_copy_from_slice(exec, buf, json.dumps(data))
```

### Memory Management

Reuse buffers when possible:

```python
# ✅ Good: Reuse buffers
temp_buf = hg.executor_allocate_buffer(executor_handle, 1024)
for _ in range(100):
    hg.vector_add_f32(executor_handle, a, b, temp_buf, 1024)
    hg.vector_mul_f32(executor_handle, temp_buf, c, output, 1024)
hg.buffer_cleanup(temp_buf)
```

### Canonical Compilation

Operations are compiled to minimal canonical forms via Sigmatics:

- Pattern rewriting reduces operation count (typical 4-8x reduction)
- Canonical forms enable lowest-latency execution
- No CPU fallbacks - all operations use canonical generators

---

## Complete Example

### Python

```python
import hologram_ffi as hg
import json

# Create executor
executor = hg.new_executor()

try:
    # Allocate buffers
    size = 1024
    a = hg.executor_allocate_buffer(executor, size)
    b = hg.executor_allocate_buffer(executor, size)
    c = hg.executor_allocate_buffer(executor, size)

    # Fill with data
    data_a = [float(i) for i in range(size)]
    data_b = [float(i * 2) for i in range(size)]

    hg.buffer_copy_from_slice(executor, a, json.dumps(data_a))
    hg.buffer_copy_from_slice(executor, b, json.dumps(data_b))

    # Perform operations
    hg.vector_add_f32(executor, a, b, c, size)
    hg.vector_relu_f32(executor, c, c, size)

    # Create tensor and perform matrix multiply
    shape = [32, 32]
    tensor_a = hg.tensor_from_buffer(a, json.dumps(shape))
    tensor_b = hg.tensor_from_buffer(b, json.dumps(shape))
    result_tensor = hg.tensor_matmul(executor, tensor_a, tensor_b)

    # Get results
    result_buf = hg.tensor_buffer(result_tensor)
    result_json = hg.buffer_to_vec(executor, result_buf)
    result_data = json.loads(result_json)

    print(f"Result: {result_data[:10]}...")  # Print first 10 elements

finally:
    # Cleanup
    hg.buffer_cleanup(a)
    hg.buffer_cleanup(b)
    hg.buffer_cleanup(c)
    hg.tensor_cleanup(tensor_a)
    hg.tensor_cleanup(tensor_b)
    hg.tensor_cleanup(result_tensor)
    hg.executor_cleanup(executor)
```

### TypeScript

```typescript
import * as hg from 'hologram-ffi';

// Create executor
const executor = hg.new_executor();

try {
    // Allocate buffers
    const size = 1024;
    const a = hg.executor_allocate_buffer(executor, size);
    const b = hg.executor_allocate_buffer(executor, size);
    const c = hg.executor_allocate_buffer(executor, size);

    // Fill with data
    const dataA = Array.from({length: size}, (_, i) => i);
    const dataB = Array.from({length: size}, (_, i) => i * 2);

    hg.buffer_copy_from_slice(executor, a, JSON.stringify(dataA));
    hg.buffer_copy_from_slice(executor, b, JSON.stringify(dataB));

    // Perform operations
    hg.vector_add_f32(executor, a, b, c, size);
    hg.vector_relu_f32(executor, c, c, size);

    // Create tensor and perform matrix multiply
    const shape = [32, 32];
    const tensorA = hg.tensor_from_buffer(a, JSON.stringify(shape));
    const tensorB = hg.tensor_from_buffer(b, JSON.stringify(shape));
    const resultTensor = hg.tensor_matmul(executor, tensorA, tensorB);

    // Get results
    const resultBuf = hg.tensor_buffer(resultTensor);
    const resultJson = hg.buffer_to_vec(executor, resultBuf);
    const resultData = JSON.parse(resultJson);

    console.log(`Result: ${resultData.slice(0, 10)}...`);

} finally {
    // Cleanup
    hg.buffer_cleanup(a);
    hg.buffer_cleanup(b);
    hg.buffer_cleanup(c);
    hg.tensor_cleanup(tensorA);
    hg.tensor_cleanup(tensorB);
    hg.tensor_cleanup(resultTensor);
    hg.executor_cleanup(executor);
}
```

---

## See Also

- [FFI Update Status](FFI_UPDATE_STATUS.md) - Implementation status and coverage
- [Hologram Core Documentation](../crates/hologram-core/README.md) - Core library documentation
- [Sigmatics Guide](SIGMATICS_GUIDE.md) - Canonical compilation system
- Python examples in `crates/hologram-ffi/interfaces/python/examples/`
- TypeScript examples in `crates/hologram-ffi/interfaces/typescript/examples/`

---

**For questions or issues**, please refer to the project documentation or file an issue on the project repository.
