# hologram-ffi

**Cross-language FFI interface for Hologram using UniFFI**

A unified Foreign Function Interface that exposes Hologram's Sigmatics-based compute functionality across multiple programming languages including Python, TypeScript, Swift, Kotlin, and WebAssembly.

## Overview

`hologram-ffi` provides a handle-based API to safely expose Rust objects across language boundaries, enabling cross-language access to Hologram's high-performance compute operations. All operations compile to canonical Sigmatics circuits under the hood, providing lowest-latency execution through pattern-based canonicalization.

## Features

- **Handle-Based Management** - Safe object lifetime management across FFI boundaries
- **Cross-Language Support** - UniFFI bindings for Python, TypeScript, Swift, Kotlin, WebAssembly
- **Executor Management** - Create and manage Sigmatics executors
- **Buffer Operations** - Typed memory buffers with copy/fill operations
- **Tensor Operations** - Multi-dimensional arrays with shape management
- **Math Operations** - Element-wise arithmetic (add, sub, mul, div, min, max)
- **Activation Functions** - Neural network activations (sigmoid, tanh, gelu, softmax)
- **Reduction Operations** - Parallel reductions (sum, min, max)
- **Loss Functions** - Training loss functions (MSE, cross-entropy, binary cross-entropy)

## Architecture

The FFI uses handle-based object management to safely expose Rust objects across language boundaries:

- **Executor** - Sigmatics circuit executor (u64 handle)
- **Buffer<T>** - Typed memory buffers (u64 handle)
- **Tensor<T>** - Multi-dimensional arrays (u64 handle)

All operations compile to canonical Sigmatics circuits under the hood, providing lowest-latency execution through pattern-based canonicalization.

## API Reference

### Executor Management

```rust
/// Create a new executor
u64 new_executor();

/// Cleanup executor
void executor_cleanup(u64 executor_handle);

/// Allocate a buffer
u64 executor_allocate_buffer(u64 executor_handle, u32 len);
```

### Buffer Operations

```rust
/// Get buffer length
u32 buffer_length(u64 buffer_handle);

/// Copy data from JSON array to buffer
void buffer_copy_from_slice(u64 executor_handle, u64 buffer_handle, string data_json);

/// Get buffer data as JSON array
string buffer_to_vec(u64 executor_handle, u64 buffer_handle);

/// Fill buffer with a value
void buffer_fill(u64 executor_handle, u64 buffer_handle, f32 value, u32 len);

/// Copy from one buffer to another
void buffer_copy(u64 executor_handle, u64 src_handle, u64 dst_handle, u32 len);

/// Cleanup buffer
void buffer_cleanup(u64 buffer_handle);
```

### Math Operations

```rust
/// Element-wise addition: c = a + b
void vector_add_f32(u64 executor_handle, u64 a_handle, u64 b_handle, u64 c_handle, u32 len);

/// Element-wise subtraction: c = a - b
void vector_sub_f32(u64 executor_handle, u64 a_handle, u64 b_handle, u64 c_handle, u32 len);

/// Element-wise multiplication: c = a * b
void vector_mul_f32(u64 executor_handle, u64 a_handle, u64 b_handle, u64 c_handle, u32 len);

/// Element-wise division: c = a / b
void vector_div_f32(u64 executor_handle, u64 a_handle, u64 b_handle, u64 c_handle, u32 len);

/// Element-wise minimum: c = min(a, b)
void vector_min_f32(u64 executor_handle, u64 a_handle, u64 b_handle, u64 c_handle, u32 len);

/// Element-wise maximum: c = max(a, b)
void vector_max_f32(u64 executor_handle, u64 a_handle, u64 b_handle, u64 c_handle, u32 len);

/// Element-wise absolute value: c = |a|
void vector_abs_f32(u64 executor_handle, u64 a_handle, u64 c_handle, u32 len);

/// Element-wise negation: c = -a
void vector_neg_f32(u64 executor_handle, u64 a_handle, u64 c_handle, u32 len);

/// Element-wise ReLU: c = max(0, a)
void vector_relu_f32(u64 executor_handle, u64 a_handle, u64 c_handle, u32 len);
```

### Reduction Operations

```rust
/// Sum reduction: output[0] = sum(input)
f32 reduce_sum_f32(u64 executor_handle, u64 input_handle, u64 output_handle, u32 len);

/// Min reduction: output[0] = min(input)
f32 reduce_min_f32(u64 executor_handle, u64 input_handle, u64 output_handle, u32 len);

/// Max reduction: output[0] = max(input)
f32 reduce_max_f32(u64 executor_handle, u64 input_handle, u64 output_handle, u32 len);
```

### Activation Functions

```rust
/// Sigmoid activation: output = 1 / (1 + exp(-input))
void sigmoid_f32(u64 executor_handle, u64 input_handle, u64 output_handle, u32 len);

/// Hyperbolic tangent: output = tanh(input)
void tanh_f32(u64 executor_handle, u64 input_handle, u64 output_handle, u32 len);

/// GELU activation
void gelu_f32(u64 executor_handle, u64 input_handle, u64 output_handle, u32 len);

/// Softmax activation: output[i] = exp(input[i]) / sum(exp(input))
void softmax_f32(u64 executor_handle, u64 input_handle, u64 output_handle, u32 len);
```

### Loss Functions

```rust
/// Mean Squared Error loss
f32 mse_loss_f32(u64 executor_handle, u64 pred_handle, u64 target_handle, u64 output_handle, u32 len);

/// Cross Entropy loss
f32 cross_entropy_loss_f32(u64 executor_handle, u64 pred_handle, u64 target_handle, u64 output_handle, u32 len);

/// Binary Cross Entropy loss
f32 binary_cross_entropy_loss_f32(u64 executor_handle, u64 pred_handle, u64 target_handle, u64 output_handle, u32 len);
```

### Tensor Operations

```rust
/// Create tensor from buffer with shape
u64 tensor_from_buffer(u64 buffer_handle, string shape_json);

/// Get tensor shape as JSON array
string tensor_shape(u64 tensor_handle);

/// Get number of dimensions
u32 tensor_ndim(u64 tensor_handle);

/// Get total number of elements
u32 tensor_numel(u64 tensor_handle);

/// Cleanup tensor
void tensor_cleanup(u64 tensor_handle);
```

## Usage Examples

### Python

```python
import hologram_ffi

# Create executor
executor = hologram_ffi.new_executor()

# Allocate buffers
a = hologram_ffi.executor_allocate_buffer(executor, 1024)
b = hologram_ffi.executor_allocate_buffer(executor, 1024)
c = hologram_ffi.executor_allocate_buffer(executor, 1024)

# Load data
data_a = [i * 1.0 for i in range(1024)]
hologram_ffi.buffer_copy_from_slice(executor, a, data_a)

# Execute operation
hologram_ffi.vector_add_f32(executor, a, b, c, 1024)

# Get results
results = hologram_ffi.buffer_to_vec(executor, c)

# Cleanup
hologram_ffi.buffer_cleanup(a)
hologram_ffi.buffer_cleanup(b)
hologram_ffi.buffer_cleanup(c)
hologram_ffi.executor_cleanup(executor)
```

### TypeScript

```typescript
import * as hologram from "hologram-ffi";

// Create executor
const executor = hologram.new_executor();

// Allocate buffers
const a = hologram.executor_allocate_buffer(executor, 1024);
const b = hologram.executor_allocate_buffer(executor, 1024);
const c = hologram.executor_allocate_buffer(executor, 1024);

// Load data
const dataA = Array.from({ length: 1024 }, (_, i) => i * 1.0);
hologram.buffer_copy_from_slice(executor, a, JSON.stringify(dataA));

// Execute operation
hologram.vector_add_f32(executor, a, b, c, 1024);

// Get results
const results = JSON.parse(hologram.buffer_to_vec(executor, c));

// Cleanup
hologram.buffer_cleanup(a);
hologram.buffer_cleanup(b);
hologram.buffer_cleanup(c);
hologram.executor_cleanup(executor);
```

## JSON Data Format

All data is passed as JSON strings:

```json
[1.0, 2.0, 3.0, 4.0]    // Array of floats
"[4, 6]"                 // Shape array
```

## Requirements

### Rust Usage

Add to your `Cargo.toml`:

```toml
[dependencies]
hologram-ffi = { path = "../../crates/hologram-ffi" }
hologram-core = { path = "../../crates/hologram-core" }
```

### Building Bindings

The crate uses UniFFI to generate bindings for various languages. Build scripts generate the necessary scaffolding:

```bash
cd crates/hologram-ffi
cargo build
```

This will generate language-specific bindings in the `interfaces/` directory.

## Dependencies

- **hologram-core** - Core hologram functionality
- **sigmatics** - Circuit canonicalization engine
- **uniffi** - Cross-language bindings framework
- **serde** - Serialization support
- **tracing** - Logging and instrumentation

## Testing

Run the test suite:

```bash
# Run all tests
cargo test

# Run with output
cargo test -- --nocapture

# Run specific module
cargo test --test buffer
```

## Safety

The handle-based API ensures safe memory management across FFI boundaries. All handles are tracked in thread-safe registries and validated before use. Invalid handle references will panic with descriptive error messages.

## Performance

All operations compile to canonical Sigmatics circuits, providing:

- **Pattern-Based Optimization** - Automatic reduction through rewrite rules
- **Canonical Compilation** - Operations compiled to optimal form
- **Generator Execution** - 7 fundamental operations execute all compute
- **Lowest Latency** - Fewer operations = faster execution

## Contributing

See the main [CLAUDE.md](../../CLAUDE.md) for development guidelines and contribution instructions.

## License

MIT OR Apache-2.0
