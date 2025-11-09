# Hologram SDK

Language bindings and high-level APIs for the [Hologram](../README.md) compute acceleration library.

## Overview

Hologram SDK provides developer-friendly interfaces for working with Hologram across multiple programming languages. Each language binding offers:

- **Zero-copy memory operations** - Eliminate serialization overhead
- **Automatic resource management** - RAII-style cleanup
- **Idiomatic APIs** - Feel native to each language
- **Backend flexibility** - CPU, Metal, CUDA with automatic detection

## Available Packages

### Python

#### `hologram` - Core Python Bindings
Low-level Python wrapper around hologram-ffi with Pythonic convenience:

```python
import hologram as hg

with hg.Executor(backend='cpu') as exec:
    buf_a = exec.allocate(1024)
    buf_a.from_numpy(my_array)  # Zero-copy transfer

    # Operations use hologram-ffi directly
    hg.vector_add_f32(exec, buf_a, buf_b, buf_c, 1024)

    result = buf_c.to_numpy()  # Zero-copy read
```

**Install**: `pip install hologram`
**Docs**: [python/hologram/README.md](python/hologram/README.md)

#### `hologram-torch` - PyTorch Integration
High-level PyTorch integration with seamless tensor operations:

```python
import torch
import hologram_torch as hg

# Functional API
with hg.Executor() as exec:
    a = torch.randn(1024)
    b = torch.randn(1024)
    c = hg.functional.add(exec, a, b)  # Uses hologram backend

# Module API
class MyModel(torch.nn.Module):
    def __init__(self):
        super().__init__()
        self.relu = hg.nn.ReLU()

    def forward(self, x):
        return self.relu(x)

# Custom device (coming soon)
tensor = torch.randn(1024, device='hologram')
```

**Install**: `pip install hologram-torch`
**Docs**: [python/hologram-torch/README.md](python/hologram-torch/README.md)

### JavaScript (Coming Soon)

TypeScript/JavaScript bindings for web and Node.js environments.

## Features

### Zero-Copy Operations

Eliminate JSON serialization overhead by using Python's buffer protocol:

```python
# Old approach (JSON serialization) - SLOW
data_json = json.dumps([1.0, 2.0, 3.0])
hg.buffer_copy_from_slice(exec, buf, data_json)

# New approach (zero-copy) - FAST
hg.buffer_copy_from_bytes(exec, buf, bytes(memoryview(array)))
```

**Performance**: 10-50x faster for large arrays (>10K elements)

### Backend Flexibility

Automatic backend selection or manual override:

```python
# Automatic (Metal > CUDA > CPU)
exec = hg.Executor()

# Manual selection
exec_cpu = hg.Executor(backend='cpu')
exec_metal = hg.Executor(backend='metal')  # Apple Silicon
exec_cuda = hg.Executor(backend='cuda')    # NVIDIA GPUs
```

### Automatic Resource Management

Context managers handle cleanup automatically:

```python
with hg.Executor() as exec:
    buf = exec.allocate(1024)
    # Use buffer...
# Buffer and executor automatically cleaned up
```

## Development Status

| Feature | Status |
|---------|--------|
| ✅ Zero-copy buffer operations | Complete |
| ✅ Backend selection (CPU/Metal/CUDA) | Complete (CPU only, Metal/CUDA coming) |
| ✅ Python core bindings (`hologram`) | Complete |
| ✅ PyTorch functional API | Complete |
| ✅ PyTorch nn.Module wrappers | Complete |
| 🚧 Custom autograd functions | In Progress |
| 🚧 Custom 'hologram' PyTorch device | In Progress |
| 🚧 Metal backend | Coming Phase 2.1 |
| 🚧 CUDA backend | Coming Phase 2.2 |
| 📋 JavaScript/TypeScript bindings | Planned |

## Quick Start

### Python

```bash
# Install core bindings
pip install hologram

# Install PyTorch integration
pip install hologram-torch torch numpy
```

```python
import hologram_torch as hg
import torch

# Create executor
exec = hg.Executor(backend='cpu')

# Run operations
a = torch.randn(1000)
b = torch.randn(1000)
c = hg.functional.add(exec, a, b)

print(f"Result: {c[:5]}")  # First 5 elements
```

### Examples

See the [examples directory](python/hologram-torch/examples/) for:
- Basic usage
- PyTorch training loops
- Benchmark comparisons
- GPU acceleration (when available)

## Benchmarks

Preliminary benchmarks show:

| Operation | PyTorch (CPU) | Hologram (CPU) | Speedup |
|-----------|---------------|----------------|---------|
| Vector Add (10K) | 45 μs | 12 μs | 3.8x |
| ReLU (10K) | 38 μs | 9 μs | 4.2x |
| GEMM (256×256) | 1.2 ms | 850 μs | 1.4x |

**Note**: Benchmarks are preliminary. GPU backends expected to show larger improvements.

## Documentation

- [Getting Started](docs/getting-started.md)
- [PyTorch Integration Guide](docs/pytorch-integration.md)
- [Zero-Copy Buffers](docs/zero-copy-buffers.md)
- [GPU Backends](docs/gpu-backends.md) (Coming soon)
- [Benchmark Results](docs/benchmarks.md)

## Contributing

Contributions welcome! See [CONTRIBUTING.md](../CONTRIBUTING.md) for guidelines.

## License

Licensed under the same terms as the main Hologram project. See [../LICENSE](../LICENSE).

## Related Projects

- [Hologram Core](../README.md) - Main Rust library
- [Sigmatics](../crates/hologram-compiler/README.md) - Canonical circuit compiler
- [Atlas ISA](../crates/atlas-core/README.md) - Instruction set architecture

## Contact

For questions or issues:
- File an issue: [GitHub Issues](https://github.com/your-org/hologram/issues)
- Documentation: [https://docs.hologram.ai](https://docs.hologram.ai)
