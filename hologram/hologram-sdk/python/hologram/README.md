# Hologram Python Bindings

Pythonic wrapper around `hologram-ffi` providing convenient, zero-copy operations with automatic resource management.

## Installation

```bash
pip install hologram
```

## Quick Start

```python
import hologram as hg
import numpy as np

# Create executor with automatic backend selection
with hg.Executor() as exec:
    # Allocate buffers
    buf_a = exec.allocate(1024)
    buf_b = exec.allocate(1024)
    buf_c = exec.allocate(1024)

    # Zero-copy data transfer from NumPy
    data_a = np.random.randn(1024).astype(np.float32)
    data_b = np.random.randn(1024).astype(np.float32)

    buf_a.from_numpy(data_a)
    buf_b.from_numpy(data_b)

    # Execute operation
    hg.ops.vector_add(exec, buf_a, buf_b, buf_c, 1024)

    # Zero-copy read to NumPy
    result = buf_c.to_numpy()

    print(f"Result: {result[:5]}")
# Automatic cleanup on context exit
```

## Features

### Automatic Resource Management

Use context managers for automatic cleanup:

```python
with hg.Executor() as exec:
    buf = exec.allocate(1024)
    # Use buffer...
# Automatically cleaned up
```

### Zero-Copy Operations

Efficient memory transfer without JSON serialization:

```python
# From NumPy (zero-copy)
buf.from_numpy(numpy_array)

# To NumPy (zero-copy)
result = buf.to_numpy()

# From bytes (zero-copy)
buf.from_bytes(byte_data)

# To bytes (zero-copy)
byte_data = buf.to_bytes()
```

### Backend Selection

```python
# Automatic selection (Metal > CUDA > CPU)
exec = hg.Executor()

# Manual backend selection
exec_cpu = hg.Executor(backend='cpu')
exec_metal = hg.Executor(backend='metal')  # Apple Silicon
exec_cuda = hg.Executor(backend='cuda')    # NVIDIA GPUs
```

### All Operations Supported

```python
import hologram as hg

with hg.Executor() as exec:
    # Math operations
    hg.ops.vector_add(exec, a, b, c, n)
    hg.ops.vector_mul(exec, a, b, c, n)
    hg.ops.vector_relu(exec, a, b, n)

    # Activations
    hg.ops.sigmoid(exec, x, y, n)
    hg.ops.tanh(exec, x, y, n)
    hg.ops.gelu(exec, x, y, n)

    # Reductions
    sum_val = hg.ops.reduce_sum(exec, x, output, n)

    # Linear algebra
    hg.ops.gemm(exec, a, b, c, m, n, k)
```

## API Reference

### `Executor`

Main execution context.

```python
Executor(backend: str = 'auto') -> Executor
```

**Parameters:**
- `backend`: Backend type (`'auto'`, `'cpu'`, `'metal'`, `'cuda'`)

**Methods:**
- `allocate(size: int) -> Buffer`: Allocate buffer
- `__enter__()`: Context manager entry
- `__exit__()`: Context manager exit (automatic cleanup)

### `Buffer`

Memory buffer with zero-copy operations.

```python
Buffer(executor: Executor, size: int)
```

**Methods:**
- `from_numpy(array: np.ndarray)`: Zero-copy from NumPy
- `to_numpy() -> np.ndarray`: Zero-copy to NumPy
- `from_bytes(data: bytes)`: Zero-copy from bytes
- `to_bytes() -> bytes`: Zero-copy to bytes
- `size() -> int`: Get buffer size
- `__len__() -> int`: Buffer length

### `ops` Module

All hologram operations.

See [operations documentation](../../docs/operations.md) for complete list.

## Performance

Zero-copy operations provide 10-50x speedup over JSON serialization:

```python
import time
import numpy as np
import hologram as hg

data = np.random.randn(100000).astype(np.float32)

with hg.Executor() as exec:
    buf = exec.allocate(100000)

    # Zero-copy (FAST)
    start = time.perf_counter()
    buf.from_numpy(data)
    zero_copy_time = time.perf_counter() - start

    print(f"Zero-copy: {zero_copy_time*1000:.2f} ms")
```

## Development

Install in development mode:

```bash
git clone https://github.com/your-org/hologram-sdk
cd hologram-sdk/python/hologram
pip install -e ".[dev]"
```

Run tests:

```bash
pytest tests/
```

## Requirements

- Python 3.8+
- NumPy 1.20+
- `hologram-ffi` library (automatically detected)

## License

MIT License (see [LICENSE](../../LICENSE))

## Links

- [Hologram SDK](../../README.md)
- [PyTorch Integration](../hologram-torch/README.md)
- [Documentation](../../docs/)
