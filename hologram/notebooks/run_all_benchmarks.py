#!/usr/bin/env python3
"""
Complete PyTorch vs Atlas Benchmark Suite - Fixed version
"""

import sys
import numpy as np
import torch
import hologram as hg
from benchmark_utils import (
    benchmark_operation,
    verify_correctness,
    collect_system_info,
)
import pandas as pd
from typing import List, Dict
import time

# Configuration
WARMUP_RUNS = 5
TIMING_RUNS = 10
RTOL = 1e-5
ATOL = 1e-8

# Test sizes
SIZES_ELEMENTWISE = [1_000, 10_000, 100_000, 1_000_000]
SIZES_REDUCTION = [1_000, 10_000, 100_000, 1_000_000]
SIZES_GEMM = [64, 128, 256]  # Keep it reasonable

# Initialize
np.random.seed(42)
torch.manual_seed(42)
torch.set_num_threads(1)
atlas_exec = hg.Executor()

print("=" * 80)
print("PYTORCH VS ATLAS COMPREHENSIVE BENCHMARK SUITE")
print("=" * 80)

# Collect system info
print("\n1. System Information:")
print("-" * 80)
sys_info = collect_system_info()
for key in ['cpu_model', 'torch_version', 'hologram_version', 'torch_num_threads']:
    if key in sys_info:
        print(f"  {key}: {sys_info[key]}")

all_results = []

def benchmark_and_verify(op_name, size, pytorch_fn, atlas_fn, is_reduction=False):
    """Helper to benchmark and verify an operation"""
    # Warmup PyTorch
    for _ in range(WARMUP_RUNS):
        _ = pytorch_fn()
    
    # Time PyTorch
    pytorch_times = []
    for _ in range(TIMING_RUNS):
        start = time.perf_counter()
        pytorch_output = pytorch_fn()
        end = time.perf_counter()
        pytorch_times.append((end - start) * 1000)  # ms
    
    # Warmup Atlas
    for _ in range(WARMUP_RUNS):
        _ = atlas_fn()
    
    # Time Atlas
    atlas_times = []
    for _ in range(TIMING_RUNS):
        start = time.perf_counter()
        atlas_output = atlas_fn()
        end = time.perf_counter()
        atlas_times.append((end - start) * 1000)  # ms
    
    # Verify correctness
    try:
        if is_reduction:
            # For reductions, outputs are scalars
            pytorch_val = pytorch_output.item() if hasattr(pytorch_output, 'item') else float(pytorch_output)
            atlas_val = float(atlas_output)
            diff = abs(pytorch_val - atlas_val)
            verified = diff < max(RTOL * abs(pytorch_val), ATOL)
        else:
            # For array operations
            pytorch_arr = pytorch_output.numpy() if hasattr(pytorch_output, 'numpy') else pytorch_output
            atlas_arr = atlas_output.to_numpy() if hasattr(atlas_output, 'to_numpy') else atlas_output
            verify_correctness(atlas_arr, pytorch_arr, rtol=RTOL, atol=ATOL, name=op_name)
            verified = True
    except Exception as e:
        print(f" ✗ Verification failed: {str(e)[:50]}")
        verified = False
    
    # Compute stats
    pytorch_mean = np.mean(pytorch_times)
    pytorch_std = np.std(pytorch_times)
    atlas_mean = np.mean(atlas_times)
    atlas_std = np.std(atlas_times)
    speedup = pytorch_mean / atlas_mean if atlas_mean > 0 else 0
    
    return {
        'operation': op_name,
        'size': size,
        'pytorch_mean_ms': pytorch_mean,
        'pytorch_std_ms': pytorch_std,
        'atlas_mean_ms': atlas_mean,
        'atlas_std_ms': atlas_std,
        'speedup': speedup,
        'verified': verified
    }


# ============================================================================
# ELEMENTWISE OPERATIONS
# ============================================================================

print("\n" + "=" * 80)
print("2. ELEMENTWISE OPERATIONS")
print("=" * 80)

for size in SIZES_ELEMENTWISE:
    print(f"\nSize {size:,}:")
    
    # Generate data
    a = np.random.randn(size).astype(np.float32)
    b = np.random.randn(size).astype(np.float32)
    
    a_torch = torch.from_numpy(a)
    b_torch = torch.from_numpy(b)
    buf_a = atlas_exec.from_numpy(a)
    buf_b = atlas_exec.from_numpy(b)
    
    # Vector Add
    print("  vector_add...", end=" ")
    result = benchmark_and_verify(
        "vector_add", size,
        lambda: torch.add(a_torch, b_torch),
        lambda: hg.ops.vector_add(buf_a, buf_b)
    )
    all_results.append(result)
    print(f"PT: {result['pytorch_mean_ms']:.3f}ms, Atlas: {result['atlas_mean_ms']:.3f}ms, Speedup: {result['speedup']:.2f}x")
    
    # Vector Mul
    print("  vector_mul...", end=" ")
    result = benchmark_and_verify(
        "vector_mul", size,
        lambda: torch.mul(a_torch, b_torch),
        lambda: hg.ops.vector_mul(buf_a, buf_b)
    )
    all_results.append(result)
    print(f"PT: {result['pytorch_mean_ms']:.3f}ms, Atlas: {result['atlas_mean_ms']:.3f}ms, Speedup: {result['speedup']:.2f}x")
    
    # Vector Div
    print("  vector_div...", end=" ")
    result = benchmark_and_verify(
        "vector_div", size,
        lambda: torch.div(a_torch, b_torch),
        lambda: hg.ops.vector_div(buf_a, buf_b)
    )
    all_results.append(result)
    print(f"PT: {result['pytorch_mean_ms']:.3f}ms, Atlas: {result['atlas_mean_ms']:.3f}ms, Speedup: {result['speedup']:.2f}x")


# ============================================================================
# UNARY OPERATIONS
# ============================================================================

print("\n" + "=" * 80)
print("3. UNARY OPERATIONS")
print("=" * 80)

for size in SIZES_ELEMENTWISE:
    print(f"\nSize {size:,}:")
    
    a = np.random.randn(size).astype(np.float32)
    a_torch = torch.from_numpy(a)
    buf_a = atlas_exec.from_numpy(a)
    
    # Neg
    print("  neg...", end=" ")
    result = benchmark_and_verify(
        "neg", size,
        lambda: torch.neg(a_torch),
        lambda: hg.ops.neg(buf_a)
    )
    all_results.append(result)
    print(f"PT: {result['pytorch_mean_ms']:.3f}ms, Atlas: {result['atlas_mean_ms']:.3f}ms, Speedup: {result['speedup']:.2f}x")
    
    # Abs
    print("  abs...", end=" ")
    result = benchmark_and_verify(
        "abs", size,
        lambda: torch.abs(a_torch),
        lambda: hg.ops.abs(buf_a)
    )
    all_results.append(result)
    print(f"PT: {result['pytorch_mean_ms']:.3f}ms, Atlas: {result['atlas_mean_ms']:.3f}ms, Speedup: {result['speedup']:.2f}x")


# ============================================================================
# ACTIVATION FUNCTIONS
# ============================================================================

print("\n" + "=" * 80)
print("4. ACTIVATION FUNCTIONS")
print("=" * 80)

for size in SIZES_ELEMENTWISE:
    print(f"\nSize {size:,}:")
    
    a = np.random.randn(size).astype(np.float32)
    a_torch = torch.from_numpy(a)
    buf_a = atlas_exec.from_numpy(a)
    
    # ReLU
    print("  relu...", end=" ")
    result = benchmark_and_verify(
        "relu", size,
        lambda: torch.relu(a_torch),
        lambda: hg.ops.relu(buf_a)
    )
    all_results.append(result)
    print(f"PT: {result['pytorch_mean_ms']:.3f}ms, Atlas: {result['atlas_mean_ms']:.3f}ms, Speedup: {result['speedup']:.2f}x")
    
    # Sigmoid
    print("  sigmoid...", end=" ")
    result = benchmark_and_verify(
        "sigmoid", size,
        lambda: torch.sigmoid(a_torch),
        lambda: hg.ops.sigmoid(buf_a)
    )
    all_results.append(result)
    print(f"PT: {result['pytorch_mean_ms']:.3f}ms, Atlas: {result['atlas_mean_ms']:.3f}ms, Speedup: {result['speedup']:.2f}x")
    
    # Tanh
    print("  tanh...", end=" ")
    result = benchmark_and_verify(
        "tanh", size,
        lambda: torch.tanh(a_torch),
        lambda: hg.ops.tanh(buf_a)
    )
    all_results.append(result)
    print(f"PT: {result['pytorch_mean_ms']:.3f}ms, Atlas: {result['atlas_mean_ms']:.3f}ms, Speedup: {result['speedup']:.2f}x")


# ============================================================================
# REDUCTION OPERATIONS
# ============================================================================

print("\n" + "=" * 80)
print("5. REDUCTION OPERATIONS")
print("=" * 80)

for size in SIZES_REDUCTION:
    print(f"\nSize {size:,}:")
    
    a = np.random.randn(size).astype(np.float32)
    a_torch = torch.from_numpy(a)
    buf_a = atlas_exec.from_numpy(a)
    
    # Sum
    print("  sum...", end=" ")
    result = benchmark_and_verify(
        "sum", size,
        lambda: torch.sum(a_torch),
        lambda: hg.ops.sum(buf_a),
        is_reduction=True
    )
    all_results.append(result)
    print(f"PT: {result['pytorch_mean_ms']:.3f}ms, Atlas: {result['atlas_mean_ms']:.3f}ms, Speedup: {result['speedup']:.2f}x")
    
    # Max
    print("  max...", end=" ")
    result = benchmark_and_verify(
        "max", size,
        lambda: torch.max(a_torch),
        lambda: hg.ops.max_reduce(buf_a),
        is_reduction=True
    )
    all_results.append(result)
    print(f"PT: {result['pytorch_mean_ms']:.3f}ms, Atlas: {result['atlas_mean_ms']:.3f}ms, Speedup: {result['speedup']:.2f}x")
    
    # Min
    print("  min...", end=" ")
    result = benchmark_and_verify(
        "min", size,
        lambda: torch.min(a_torch),
        lambda: hg.ops.min_reduce(buf_a),
        is_reduction=True
    )
    all_results.append(result)
    print(f"PT: {result['pytorch_mean_ms']:.3f}ms, Atlas: {result['atlas_mean_ms']:.3f}ms, Speedup: {result['speedup']:.2f}x")


# ============================================================================
# GEMM
# ============================================================================

print("\n" + "=" * 80)
print("6. GEMM (Matrix Multiplication)")
print("=" * 80)

for size in SIZES_GEMM:
    print(f"\nMatrix {size}×{size}:")
    
    A = np.random.randn(size, size).astype(np.float32)
    B = np.random.randn(size, size).astype(np.float32)
    
    A_torch = torch.from_numpy(A)
    B_torch = torch.from_numpy(B)
    
    A_flat = A.flatten()
    B_flat = B.flatten()
    buf_A = atlas_exec.from_numpy(A_flat)
    buf_B = atlas_exec.from_numpy(B_flat)
    
    print("  gemm...", end=" ")
    
    # Custom verification for GEMM (needs reshaping)
    for _ in range(WARMUP_RUNS):
        _ = torch.matmul(A_torch, B_torch)
    
    pytorch_times = []
    for _ in range(TIMING_RUNS):
        start = time.perf_counter()
        pytorch_output = torch.matmul(A_torch, B_torch)
        end = time.perf_counter()
        pytorch_times.append((end - start) * 1000)
    
    for _ in range(WARMUP_RUNS):
        _ = hg.ops.gemm(buf_A, buf_B, m=size, n=size, k=size)
    
    atlas_times = []
    for _ in range(TIMING_RUNS):
        start = time.perf_counter()
        atlas_output = hg.ops.gemm(buf_A, buf_B, m=size, n=size, k=size)
        end = time.perf_counter()
        atlas_times.append((end - start) * 1000)
    
    # Verify
    try:
        atlas_arr = atlas_output.to_numpy().reshape(size, size)
        pytorch_arr = pytorch_output.numpy()
        verify_correctness(atlas_arr, pytorch_arr, rtol=RTOL, atol=ATOL, name="gemm")
        verified = True
    except Exception as e:
        print(f" ✗ Failed: {str(e)[:30]}")
        verified = False
    
    pytorch_mean = np.mean(pytorch_times)
    atlas_mean = np.mean(atlas_times)
    speedup = pytorch_mean / atlas_mean if atlas_mean > 0 else 0
    
    result = {
        'operation': f'gemm_{size}x{size}',
        'size': size * size,
        'pytorch_mean_ms': pytorch_mean,
        'pytorch_std_ms': np.std(pytorch_times),
        'atlas_mean_ms': atlas_mean,
        'atlas_std_ms': np.std(atlas_times),
        'speedup': speedup,
        'verified': verified
    }
    all_results.append(result)
    print(f"PT: {result['pytorch_mean_ms']:.3f}ms, Atlas: {result['atlas_mean_ms']:.3f}ms, Speedup: {speedup:.2f}x")


# ============================================================================
# SUMMARY
# ============================================================================

print("\n" + "=" * 80)
print("7. SUMMARY")
print("=" * 80)

df = pd.DataFrame(all_results)

print(f"\nTotal benchmarks: {len(df)}")
print(f"Verified: {df['verified'].sum()}/{len(df)}")

print("\nAverage Speedup by Operation:")
print("-" * 80)
speedup_by_op = df.groupby('operation')['speedup'].mean().sort_values(ascending=False)
for op, speedup in speedup_by_op.items():
    winner = "Atlas" if speedup > 1.0 else "PyTorch"
    print(f"  {op:20s}: {speedup:.2f}x - {winner} wins")

# Save
output_file = "benchmark_results.csv"
df.to_csv(output_file, index=False)
print(f"\n✅ Results saved to: {output_file}")

print("\n" + "=" * 80)
print("COMPLETE ✓")
print("=" * 80)
