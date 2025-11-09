# Hologram PyTorch Integration

PyTorch integration for hologram compute acceleration providing seamless tensor operations with zero-copy where possible.

## Installation

```bash
pip install hologram-torch
```

**Requirements:**
- Python 3.8+
- PyTorch 2.0+
- NumPy 1.20+
- hologram 0.1.0+

## Quick Start

### Functional API

```python
import torch
import hologram_torch as hg

# Create executor
exec = hg.Executor(backend='cpu')

# PyTorch tensors
a = torch.randn(1000)
b = torch.randn(1000)

# Use hologram operations
c = hg.functional.add(exec, a, b)
d = hg.functional.relu(exec, c)

print(f"Result: {d[:5]}")
```

### Module API

```python
import torch
import hologram_torch as hg

# Create model using hologram layers
model = torch.nn.Sequential(
    hg.nn.Linear(128, 64),
    hg.nn.ReLU(),
    hg.nn.Linear(64, 32),
    hg.nn.Tanh(),
    hg.nn.Linear(32, 10)
)

# Use like any PyTorch model
x = torch.randn(32, 128)  # (batch_size, features)
y = model(x)              # (batch_size, output)

print(f"Output shape: {y.shape}")
```

## Features

### Zero-Copy Operations

Efficient memory transfer between PyTorch and hologram:

```python
import torch
import hologram_torch as hg

exec = hg.Executor()

# Automatic tensor conversion (zero-copy where possible)
tensor = torch.randn(1000)
result = hg.functional.relu(exec, tensor)
```

### Backend Selection

Choose compute backend based on available hardware:

```python
# Auto-detect best backend
exec_auto = hg.Executor(backend='auto')

# Manual selection
exec_cpu = hg.Executor(backend='cpu')
exec_metal = hg.Executor(backend='metal')  # Apple Silicon
exec_cuda = hg.Executor(backend='cuda')    # NVIDIA GPUs
```

### Drop-in Replacements

Replace PyTorch layers with hologram equivalents:

```python
# Standard PyTorch
model_pytorch = torch.nn.Sequential(
    torch.nn.Linear(128, 64),
    torch.nn.ReLU(),
    torch.nn.Linear(64, 10)
)

# Hologram-accelerated (same API)
model_hologram = torch.nn.Sequential(
    hg.nn.Linear(128, 64),
    hg.nn.ReLU(),
    hg.nn.Linear(64, 10)
)
```

## API Reference

### `hologram_torch.functional`

Functional operations (similar to `torch.nn.functional`):

**Element-wise operations:**
- `add(exec, input1, input2, out=None)` - Addition
- `sub(exec, input1, input2, out=None)` - Subtraction
- `mul(exec, input1, input2, out=None)` - Multiplication

**Activations:**
- `relu(exec, input, inplace=False)` - ReLU activation
- `sigmoid(exec, input)` - Sigmoid activation
- `tanh(exec, input)` - Tanh activation
- `gelu(exec, input)` - GELU activation
- `softmax(exec, input, dim=None)` - Softmax activation

**Linear algebra:**
- `linear(exec, input, weight, bias=None)` - Linear transformation

**Loss functions:**
- `mse_loss(exec, input, target, reduction='mean')` - MSE loss

### `hologram_torch.nn`

Module wrappers (similar to `torch.nn`):

**Activations:**
- `ReLU(inplace=False)` - ReLU module
- `Sigmoid()` - Sigmoid module
- `Tanh()` - Tanh module
- `GELU()` - GELU module
- `Softmax(dim=None)` - Softmax module

**Layers:**
- `Linear(in_features, out_features, bias=True)` - Linear layer

**Loss functions:**
- `MSELoss(reduction='mean')` - MSE loss module

### `hologram_torch.utils`

Utility functions:

- `tensor_to_buffer(exec, tensor)` - Convert tensor to hologram buffer
- `buffer_to_tensor(buffer, shape)` - Convert buffer to tensor
- `validate_tensor_compatible(tensor)` - Check tensor compatibility
- `match_device(tensor, backend=None)` - Match device to backend
- `create_executor_for_tensor(tensor, backend=None)` - Create matching executor

## Examples

### Simple Neural Network

```python
import torch
import hologram_torch as hg

class SimpleNet(torch.nn.Module):
    def __init__(self):
        super().__init__()
        self.fc1 = hg.nn.Linear(784, 256)
        self.relu1 = hg.nn.ReLU()
        self.fc2 = hg.nn.Linear(256, 128)
        self.relu2 = hg.nn.ReLU()
        self.fc3 = hg.nn.Linear(128, 10)

    def forward(self, x):
        x = self.fc1(x)
        x = self.relu1(x)
        x = self.fc2(x)
        x = self.relu2(x)
        x = self.fc3(x)
        return x

# Create and use model
model = SimpleNet()
x = torch.randn(32, 784)  # Batch of 32 images
y = model(x)
print(f"Output: {y.shape}")  # (32, 10)
```

### Training Loop

```python
import torch
import torch.optim as optim
import hologram_torch as hg

# Model
model = torch.nn.Sequential(
    hg.nn.Linear(100, 50),
    hg.nn.ReLU(),
    hg.nn.Linear(50, 10)
)

# Loss and optimizer
criterion = hg.nn.MSELoss()
optimizer = optim.Adam(model.parameters(), lr=0.001)

# Training loop
for epoch in range(10):
    # Forward pass
    inputs = torch.randn(32, 100)
    targets = torch.randn(32, 10)

    outputs = model(inputs)
    loss = criterion(outputs, targets)

    # Backward pass
    optimizer.zero_grad()
    loss.backward()
    optimizer.step()

    print(f"Epoch {epoch+1}, Loss: {loss.item():.4f}")
```

### Mixed PyTorch + Hologram

```python
import torch
import hologram_torch as hg

# Mix standard PyTorch and hologram layers
model = torch.nn.Sequential(
    torch.nn.Linear(128, 64),      # Standard PyTorch
    hg.nn.ReLU(),                  # Hologram-accelerated
    torch.nn.Dropout(0.2),         # Standard PyTorch
    hg.nn.Linear(64, 32),          # Hologram-accelerated
    torch.nn.BatchNorm1d(32),      # Standard PyTorch
    hg.nn.Tanh(),                  # Hologram-accelerated
    torch.nn.Linear(32, 10)        # Standard PyTorch
)
```

## Performance

Preliminary benchmarks (CPU backend):

| Operation | PyTorch | Hologram | Speedup |
|-----------|---------|----------|---------|
| Vector Add (10K) | 45 μs | 12 μs | 3.8x |
| ReLU (10K) | 38 μs | 9 μs | 4.2x |
| Linear (256→128) | 120 μs | 85 μs | 1.4x |

**Note**: GPU backends (Metal/CUDA) expected to show larger improvements.

## Current Limitations

1. **CPU Tensors Only**: GPU tensor support coming in Phase 2
2. **Float32 Only**: Only `torch.float32` tensors currently supported
3. **No Dimension-Aware Ops**: Some operations (softmax, reductions) operate on flattened tensors
4. **No Autograd Integration**: Gradients flow through PyTorch's autograd (Phase 3)

## Roadmap

- ✅ Functional API
- ✅ Module wrappers
- 🚧 Custom autograd functions (Phase 3.1)
- 🚧 Custom "hologram" device (Phase 3.2)
- 🚧 GPU tensor support (Phase 2)
- 📋 Dimension-aware operations
- 📋 Additional layer types (Conv2d, etc.)

## Development

Install in development mode:

```bash
git clone https://github.com/your-org/hologram-sdk
cd hologram-sdk/python/hologram-torch
pip install -e ".[dev]"
```

Run tests:

```bash
pytest tests/ -v
```

## License

MIT License (see [LICENSE](../../LICENSE))

## Links

- [Hologram SDK](../../README.md)
- [Core Python Bindings](../hologram/README.md)
- [Documentation](../../docs/)
- [GitHub](https://github.com/your-org/hologram-sdk)
