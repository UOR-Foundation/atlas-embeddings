# Hologram SDK Testing Guide

**Date:** 2025-10-30
**Phase:** 1.6 - Integration Tests & Benchmarks

---

## Overview

This guide covers running integration tests and benchmarks for the hologram SDK packages:
- `hologram` - Core Python bindings
- `hologram-torch` - PyTorch integration

---

## Prerequisites

### 1. Build hologram-ffi

```bash
cd /workspace
cargo build-ffi
```

### 2. Install Python dependencies

```bash
# Install hologram core
cd /workspace/hologram-sdk/python/hologram
pip install -e ".[dev]"

# Install hologram-torch
cd /workspace/hologram-sdk/python/hologram-torch
pip install -e ".[dev]"
```

Required packages:
- `numpy>=1.20.0`
- `torch>=2.0.0`
- `pytest>=7.0.0`
- `pytest-benchmark>=4.0.0`

---

## Integration Tests

### hologram (Core Bindings)

**Location:** `/workspace/hologram-sdk/python/hologram/tests/`

**Run all tests:**
```bash
cd /workspace/hologram-sdk/python/hologram
pytest tests/ -v
```

**Run specific test files:**
```bash
# Unit tests
pytest tests/test_basic.py -v

# Integration tests
pytest tests/test_integration.py -v
```

**Test coverage:**
- ✅ Backend utilities (CPU/Metal/CUDA detection)
- ✅ Executor creation and cleanup
- ✅ Buffer allocation and operations
- ✅ Zero-copy roundtrip (NumPy ↔ buffer)
- ✅ All operation wrappers (math, activation, reduce, loss, linalg)
- ✅ Complete workflows (multi-operation chains)
- ✅ Matrix multiplication
- ✅ Large-scale operations (100K elements)
- ✅ Error handling and edge cases

**Expected results:**
```
test_integration.py::TestIntegrationWorkflows::test_complete_vector_operation_workflow PASSED
test_integration.py::TestIntegrationWorkflows::test_chained_operations PASSED
test_integration.py::TestIntegrationWorkflows::test_reduction_workflow PASSED
test_integration.py::TestIntegrationWorkflows::test_matrix_multiplication_workflow PASSED
test_integration.py::TestIntegrationWorkflows::test_activation_functions_workflow PASSED
test_integration.py::TestIntegrationWorkflows::test_buffer_copy_and_fill PASSED
test_integration.py::TestIntegrationWorkflows::test_zero_copy_roundtrip_performance PASSED
test_integration.py::TestIntegrationWorkflows::test_large_scale_operation PASSED
test_integration.py::TestErrorHandling::test_size_mismatch_error PASSED
test_integration.py::TestErrorHandling::test_wrong_dtype_error PASSED
test_integration.py::TestErrorHandling::test_freed_buffer_error PASSED
test_integration.py::TestErrorHandling::test_invalid_backend PASSED
test_integration.py::TestErrorHandling::test_reduction_buffer_size_error PASSED
```

---

### hologram-torch (PyTorch Integration)

**Location:** `/workspace/hologram-sdk/python/hologram-torch/tests/`

**Run all tests:**
```bash
cd /workspace/hologram-sdk/python/hologram-torch
pytest tests/ -v
```

**Run specific test classes:**
```bash
# Functional API tests
pytest tests/test_integration.py::TestFunctionalAPIIntegration -v

# Module API tests
pytest tests/test_integration.py::TestModuleAPIIntegration -v

# Training tests
pytest tests/test_integration.py::TestTrainingIntegration -v

# Large-scale tests
pytest tests/test_integration.py::TestLargeScale -v
```

**Test coverage:**
- ✅ Functional API (add, mul, sub, relu, sigmoid, tanh, gelu, linear, mse_loss)
- ✅ Module API (Linear, ReLU, Sigmoid, Tanh, GELU, MSELoss)
- ✅ Tensor conversion utilities
- ✅ Training workflows (forward, backward, optimizer)
- ✅ Mixed PyTorch + hologram networks
- ✅ Multi-dimensional tensors
- ✅ Large-scale operations (100K elements)
- ✅ Gradient flow verification
- ✅ Error handling

**Expected results:**
```
test_integration.py::TestFunctionalAPIIntegration::test_basic_tensor_operations PASSED
test_integration.py::TestFunctionalAPIIntegration::test_activation_functions PASSED
test_integration.py::TestFunctionalAPIIntegration::test_linear_transformation PASSED
test_integration.py::TestFunctionalAPIIntegration::test_loss_function PASSED
test_integration.py::TestFunctionalAPIIntegration::test_chained_operations PASSED
test_integration.py::TestModuleAPIIntegration::test_linear_module PASSED
test_integration.py::TestModuleAPIIntegration::test_activation_modules PASSED
test_integration.py::TestModuleAPIIntegration::test_simple_network PASSED
test_integration.py::TestModuleAPIIntegration::test_mixed_pytorch_hologram_network PASSED
test_integration.py::TestTrainingIntegration::test_forward_backward_pass PASSED
test_integration.py::TestTrainingIntegration::test_training_loop PASSED
test_integration.py::TestTrainingIntegration::test_gradients_flow PASSED
test_integration.py::TestTensorConversionUtils::test_tensor_to_buffer_roundtrip PASSED
test_integration.py::TestTensorConversionUtils::test_validate_tensor_compatible PASSED
test_integration.py::TestTensorConversionUtils::test_multidimensional_tensors PASSED
test_integration.py::TestLargeScale::test_large_tensor_operation PASSED
test_integration.py::TestLargeScale::test_large_network_forward PASSED
test_integration.py::TestErrorHandling::test_shape_mismatch_error PASSED
```

---

## Benchmarks

### Zero-Copy Performance

**Location:** `/workspace/hologram-sdk/python/hologram-torch/benchmarks/bench_zero_copy.py`

**Run benchmark:**
```bash
cd /workspace/hologram-sdk/python/hologram-torch
python benchmarks/bench_zero_copy.py
```

**What it measures:**
- **Write performance** (Host → Device): JSON vs zero-copy
- **Read performance** (Device → Host): JSON vs zero-copy
- **Total round-trip**: JSON vs zero-copy
- **Multiple sizes**: 100, 1K, 10K, 100K elements

**Output:**
- Console output with detailed timing
- Markdown report saved to `/workspace/docs/hologram-sdk/ZERO_COPY_BENCHMARKS.md`

**Expected speedup:**
- Small arrays (100 elements): 2-5x
- Medium arrays (1K-10K): 10-20x
- Large arrays (100K): 20-50x

---

## Running All Tests

**Complete test suite:**
```bash
#!/bin/bash

# Core bindings tests
echo "Testing hologram (core bindings)..."
cd /workspace/hologram-sdk/python/hologram
pytest tests/ -v

# PyTorch integration tests
echo "Testing hologram-torch..."
cd /workspace/hologram-sdk/python/hologram-torch
pytest tests/ -v

# Run benchmarks
echo "Running zero-copy benchmarks..."
python benchmarks/bench_zero_copy.py

echo "All tests complete!"
```

---

## Continuous Integration

### GitHub Actions Workflow

Create `.github/workflows/test-sdk.yml`:

```yaml
name: Test hologram SDK

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest

    steps:
    - uses: actions/checkout@v3

    - name: Set up Rust
      uses: actions-rs/toolchain@v1
      with:
        toolchain: stable

    - name: Build hologram-ffi
      run: cargo build-ffi

    - name: Set up Python
      uses: actions/setup-python@v4
      with:
        python-version: '3.10'

    - name: Install dependencies
      run: |
        pip install pytest pytest-benchmark numpy torch
        pip install -e hologram-sdk/python/hologram
        pip install -e hologram-sdk/python/hologram-torch

    - name: Run hologram tests
      run: |
        cd hologram-sdk/python/hologram
        pytest tests/ -v

    - name: Run hologram-torch tests
      run: |
        cd hologram-sdk/python/hologram-torch
        pytest tests/ -v

    - name: Run benchmarks
      run: |
        cd hologram-sdk/python/hologram-torch
        python benchmarks/bench_zero_copy.py
```

---

## Troubleshooting

### hologram_ffi not found

**Error:**
```
ImportError: hologram_ffi not found
```

**Solution:**
```bash
cd /workspace
cargo build-ffi
# Ensure libhologram_ffi.so is in Python's path
```

### Tests skip due to missing dependencies

**Error:**
```
SKIPPED [1] tests/test_integration.py:9: hologram_ffi not available
```

**Solution:**
1. Build hologram-ffi: `cargo build-ffi`
2. Install packages in development mode
3. Verify import: `python -c "import hologram_ffi"`

### Numerical precision issues

**Error:**
```
AssertionError: Tensor-likes are not close!
```

**Solution:**
- Increase tolerance: `rtol=1e-4, atol=1e-4`
- Floating-point operations may have small differences
- This is expected for complex operations

### CUDA tests fail

**Error:**
```
ValueError: Only CPU tensors supported
```

**Solution:**
- GPU tensor support coming in Phase 2
- Use CPU tensors for now: `tensor.cpu()`

---

## Test Statistics

### hologram (Core Bindings)

- **Unit tests:** 15 tests
- **Integration tests:** 13 tests
- **Total coverage:** 28 tests
- **Expected runtime:** ~5-10 seconds

### hologram-torch (PyTorch Integration)

- **Functional API tests:** 5 tests
- **Module API tests:** 4 tests
- **Training tests:** 3 tests
- **Tensor utils tests:** 3 tests
- **Large-scale tests:** 2 tests
- **Error handling tests:** 2 tests
- **Total coverage:** 19 tests
- **Expected runtime:** ~10-20 seconds

---

## Next Steps

After running all tests successfully:

1. ✅ **Phase 1 Complete** - All foundational work validated
2. 🚧 **Phase 2.1** - Implement Metal backend (Apple Silicon)
3. 🚧 **Phase 2.2** - Implement CUDA backend (NVIDIA GPUs)
4. 🚧 **Phase 3** - Custom autograd and device support
5. 🚧 **Phase 4** - Additional benchmarks and documentation

---

## Support

For issues or questions:
- File an issue: [GitHub Issues](https://github.com/your-org/hologram/issues)
- Check documentation: `/workspace/docs/hologram-sdk/`
- Review examples: `/workspace/hologram-sdk/python/*/examples/`

---

**Last Updated:** 2025-10-30
