#!/usr/bin/env python3
"""
Basic usage example for hologram Python bindings.

Demonstrates:
- Executor context manager
- Buffer allocation
- Zero-copy NumPy integration
- Vector addition operation
"""

import numpy as np
import hologram as hg


def main():
    print("=" * 60)
    print("Hologram Python Bindings - Basic Usage Example")
    print("=" * 60)
    print()

    # Check available backends
    print("Available backends:")
    print(f"  CPU: Always available")
    print(f"  Metal: {hg.is_metal_available()}")
    print(f"  CUDA: {hg.is_cuda_available()}")
    print(f"  Default: {hg.get_default_backend()}")
    print()

    # Create executor with automatic backend selection
    print("Creating executor with automatic backend selection...")
    with hg.Executor(backend='auto') as exec:
        print(f"Executor created: {exec}")
        print(f"Backend: {exec.backend}")
        print()

        # Allocate buffers
        print("Allocating buffers (1024 elements each)...")
        buf_a = exec.allocate(1024)
        buf_b = exec.allocate(1024)
        buf_c = exec.allocate(1024)
        print(f"  buf_a: {buf_a}")
        print(f"  buf_b: {buf_b}")
        print(f"  buf_c: {buf_c}")
        print()

        # Create test data
        print("Creating test data...")
        data_a = np.arange(1024, dtype=np.float32)
        data_b = np.arange(1024, dtype=np.float32) * 2.0
        print(f"  data_a shape: {data_a.shape}, dtype: {data_a.dtype}")
        print(f"  data_b shape: {data_b.shape}, dtype: {data_b.dtype}")
        print(f"  data_a[:5] = {data_a[:5]}")
        print(f"  data_b[:5] = {data_b[:5]}")
        print()

        # Zero-copy transfer to buffers
        print("Transferring data to buffers (zero-copy)...")
        buf_a.from_numpy(data_a)
        buf_b.from_numpy(data_b)
        print("  Transfer complete")
        print()

        # Execute vector addition
        print("Executing vector addition: c = a + b...")
        hg.ops.vector_add(exec, buf_a, buf_b, buf_c)
        print("  Operation complete")
        print()

        # Read results (zero-copy)
        print("Reading results from buffer (zero-copy)...")
        result = buf_c.to_numpy()
        print(f"  result shape: {result.shape}, dtype: {result.dtype}")
        print(f"  result[:5] = {result[:5]}")
        print()

        # Verify correctness
        print("Verifying results...")
        expected = data_a + data_b
        np.testing.assert_allclose(result, expected, rtol=1e-5)
        print("  ✓ Results match expected values!")
        print()

        # Demonstrate fill operation
        print("Testing buffer fill operation...")
        buf_a.fill(42.0)
        result_filled = buf_a.to_numpy()
        print(f"  After fill(42.0): {result_filled[:5]}")
        assert np.all(result_filled == 42.0), "Fill failed"
        print("  ✓ Fill operation successful!")
        print()

        # Demonstrate buffer copy
        print("Testing buffer copy operation...")
        buf_b.fill(123.0)
        buf_a.copy_from(buf_b)
        result_copied = buf_a.to_numpy()
        print(f"  After copy_from(buf_b): {result_copied[:5]}")
        assert np.all(result_copied == 123.0), "Copy failed"
        print("  ✓ Copy operation successful!")
        print()

    # Automatic cleanup when context exits
    print("Executor context exited - automatic cleanup complete")
    print()
    print("=" * 60)
    print("Example completed successfully!")
    print("=" * 60)


if __name__ == "__main__":
    main()
