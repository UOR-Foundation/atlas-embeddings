"""
Benchmark Harness for PyTorch vs Atlas Performance Comparison

This module provides utilities for fair, reproducible benchmarking of operations
across PyTorch CPU and Hologram Atlas, implementing warm kernel methodology
to exclude compilation/JIT overhead.

Key Features:
- Warm kernel benchmarking (exclude compilation overhead)
- Statistical analysis (min/max/mean/median/std, confidence intervals)
- Correctness verification
- Visualization helpers
- System information collection

Author: Generated for hologramapp
Version: 0.1.0
"""

import time
import warnings
import platform
import datetime
import json
from dataclasses import dataclass, asdict
from typing import Callable, List, Dict, Any, Optional, Tuple
import numpy as np

__version__ = "0.1.0"

# ============================================================================
# Core Data Structures
# ============================================================================

@dataclass
class BenchmarkResult:
    """
    Container for benchmark timing results
    
    Attributes:
        name: Operation name
        framework: "pytorch" or "atlas"
        size: Input size (number of elements)
        dtype: Data type (e.g., "float32")
        times_sec: Raw timing measurements in seconds
        warmup_runs: Number of warmup iterations
        timing_runs: Number of timed iterations
        min_ms: Minimum time in milliseconds
        max_ms: Maximum time in milliseconds
        mean_ms: Mean time in milliseconds
        median_ms: Median time in milliseconds
        std_ms: Standard deviation in milliseconds
        ci_95: 95% confidence interval for mean (lower, upper)
        outliers: List of indices of outlier runs
        cv: Coefficient of variation (std/mean)
        throughput_gops: Optional throughput in GFLOP/s
        bandwidth_gbs: Optional memory bandwidth in GB/s
    """
    
    # Metadata
    name: str
    framework: str = "unknown"
    size: int = 0
    dtype: str = "float32"
    
    # Timing data
    times_sec: List[float] = None
    warmup_runs: int = 5
    timing_runs: int = 10
    
    # Statistics (milliseconds)
    min_ms: float = 0.0
    max_ms: float = 0.0
    mean_ms: float = 0.0
    median_ms: float = 0.0
    std_ms: float = 0.0
    ci_95: Tuple[float, float] = (0.0, 0.0)
    
    # Quality metrics
    outliers: List[int] = None
    cv: float = 0.0
    
    # Derived metrics (optional)
    throughput_gops: Optional[float] = None
    bandwidth_gbs: Optional[float] = None
    
    def __post_init__(self):
        if self.times_sec is None:
            self.times_sec = []
        if self.outliers is None:
            self.outliers = []
    
    @property
    def is_reliable(self) -> bool:
        """Check if results are reliable (CV < 0.1, few outliers)"""
        return self.cv < 0.1 and len(self.outliers) < self.timing_runs * 0.2
    
    def to_dict(self) -> dict:
        """Convert to dictionary for serialization"""
        return asdict(self)
    
    def __repr__(self) -> str:
        return (
            f"BenchmarkResult(name='{self.name}', framework='{self.framework}', "
            f"mean={self.mean_ms:.3f}ms ± {self.std_ms:.3f}ms, "
            f"reliable={self.is_reliable})"
        )


# ============================================================================
# Statistical Utilities
# ============================================================================

def compute_stats(times: List[float]) -> Dict[str, Any]:
    """
    Compute statistical measures for timing data
    
    Args:
        times: List of timing measurements in seconds
    
    Returns:
        Dictionary with min, max, mean, median, std, ci_95, cv
    """
    times_arr = np.array(times)
    
    # Basic statistics
    min_time = np.min(times_arr)
    max_time = np.max(times_arr)
    mean_time = np.mean(times_arr)
    median_time = np.median(times_arr)
    std_time = np.std(times_arr, ddof=1) if len(times) > 1 else 0.0
    
    # 95% confidence interval for mean
    n = len(times)
    if n > 1:
        try:
            from scipy import stats as scipy_stats
            ci_95 = scipy_stats.t.interval(
                0.95,
                df=n-1,
                loc=mean_time,
                scale=std_time / np.sqrt(n)
            )
        except ImportError:
            # Fallback: approximate with 1.96 * std / sqrt(n)
            margin = 1.96 * std_time / np.sqrt(n)
            ci_95 = (mean_time - margin, mean_time + margin)
    else:
        ci_95 = (mean_time, mean_time)
    
    # Coefficient of variation
    cv = std_time / mean_time if mean_time > 0 else float('inf')
    
    return {
        'min': min_time,
        'max': max_time,
        'mean': mean_time,
        'median': median_time,
        'std': std_time,
        'ci_95': ci_95,
        'cv': cv
    }


def detect_outliers(
    times: List[float],
    method: str = "iqr",
    threshold: float = 1.5
) -> List[int]:
    """
    Detect outlier measurements using IQR or Z-score method
    
    Args:
        times: List of timing measurements
        method: "iqr" (interquartile range) or "zscore"
        threshold: Multiplier for outlier detection (1.5 for IQR, 3.0 for Z-score)
    
    Returns:
        List of indices of outlier measurements
    """
    times_arr = np.array(times)
    
    if len(times_arr) < 3:
        return []  # Not enough data for outlier detection
    
    if method == "iqr":
        q1, q3 = np.percentile(times_arr, [25, 75])
        iqr = q3 - q1
        lower = q1 - threshold * iqr
        upper = q3 + threshold * iqr
        outliers = np.where((times_arr < lower) | (times_arr > upper))[0]
    
    elif method == "zscore":
        mean = np.mean(times_arr)
        std = np.std(times_arr, ddof=1)
        if std == 0:
            return []
        z_scores = np.abs((times_arr - mean) / std)
        outliers = np.where(z_scores > threshold)[0]
    
    else:
        raise ValueError(f"Unknown method: {method}")
    
    return outliers.tolist()


# ============================================================================
# Core Benchmarking Function
# ============================================================================

def benchmark_operation(
    operation_fn: Callable,
    *args,
    warmup_runs: int = 5,
    timing_runs: int = 10,
    verify_fn: Optional[Callable] = None,
    synchronize_fn: Optional[Callable] = None,
    name: str = "operation",
    framework: str = "unknown",
    size: int = 0,
    dtype: str = "float32"
) -> BenchmarkResult:
    """
    Benchmark an operation with warm kernels and statistical analysis
    
    This function implements the warm kernel methodology:
    1. Warmup phase: Run operation N times to warm up caches, compile kernels
    2. Timing phase: Run operation M times with precise timing
    3. Statistical analysis: Compute mean, median, std, confidence intervals
    4. Outlier detection: Identify and report anomalous runs
    
    Args:
        operation_fn: Function to benchmark (must be callable)
        *args: Arguments to pass to operation_fn
        warmup_runs: Number of warmup iterations (default 5)
        timing_runs: Number of timed iterations (default 10)
        verify_fn: Optional verification function verify_fn(result) -> bool
        synchronize_fn: Optional synchronization function (e.g., torch.cuda.synchronize)
        name: Operation name for logging
        framework: Framework name ("pytorch" or "atlas")
        size: Input size for metadata
        dtype: Data type for metadata
    
    Returns:
        BenchmarkResult with timing statistics
    
    Example:
        >>> def add(a, b):
        ...     return a + b
        >>> result = benchmark_operation(add, x, y, name="vector_add")
        >>> print(f"Mean: {result.mean_ms:.3f} ms")
    """
    
    # 1. Warmup phase
    for i in range(warmup_runs):
        result = operation_fn(*args)
        if synchronize_fn:
            synchronize_fn()
    
    # 2. Timing phase
    times = []
    for i in range(timing_runs):
        start = time.perf_counter()
        result = operation_fn(*args)
        if synchronize_fn:
            synchronize_fn()
        end = time.perf_counter()
        times.append(end - start)
    
    # 3. Verify correctness (optional)
    if verify_fn:
        if not verify_fn(result):
            raise ValueError(f"Verification failed for {name}")
    
    # 4. Compute statistics
    stats = compute_stats(times)
    
    # 5. Detect outliers
    outliers = detect_outliers(times)
    if len(outliers) > timing_runs * 0.2:  # >20% outliers
        warnings.warn(
            f"{name}: {len(outliers)}/{timing_runs} outlier runs detected "
            f"(CV={stats['cv']:.3f}). Results may be unreliable."
        )
    
    # 6. Return structured result
    return BenchmarkResult(
        name=name,
        framework=framework,
        size=size,
        dtype=dtype,
        times_sec=times,
        warmup_runs=warmup_runs,
        timing_runs=timing_runs,
        min_ms=stats['min'] * 1000,
        max_ms=stats['max'] * 1000,
        mean_ms=stats['mean'] * 1000,
        median_ms=stats['median'] * 1000,
        std_ms=stats['std'] * 1000,
        ci_95=tuple(c * 1000 for c in stats['ci_95']),
        outliers=outliers,
        cv=stats['cv']
    )


# Placeholder for remaining functions - will be implemented next


# ============================================================================
# Correctness Verification
# ============================================================================

def verify_correctness(
    result: np.ndarray,
    expected: np.ndarray,
    rtol: float = 1e-5,
    atol: float = 1e-8,
    name: str = "operation"
) -> bool:
    """
    Verify operation correctness against expected result
    
    Args:
        result: Computed result
        expected: Expected result
        rtol: Relative tolerance
        atol: Absolute tolerance
        name: Operation name for error messages
    
    Returns:
        True if results match within tolerance
    
    Raises:
        ValueError: If results don't match with detailed error info
    """
    if result.shape != expected.shape:
        raise ValueError(
            f"{name}: Shape mismatch - "
            f"got {result.shape}, expected {expected.shape}"
        )
    
    if result.dtype != expected.dtype:
        warnings.warn(
            f"{name}: dtype mismatch - "
            f"got {result.dtype}, expected {expected.dtype}"
        )
    
    if not np.allclose(result, expected, rtol=rtol, atol=atol):
        # Find worst mismatch
        diff = np.abs(result - expected)
        max_diff_idx = np.argmax(diff)
        max_diff = diff.flat[max_diff_idx]
        
        raise ValueError(
            f"{name}: Results don't match\n"
            f"  Max absolute difference: {max_diff:.2e}\n"
            f"  At index: {max_diff_idx}\n"
            f"  Got: {result.flat[max_diff_idx]}\n"
            f"  Expected: {expected.flat[max_diff_idx]}\n"
            f"  Tolerance: rtol={rtol}, atol={atol}"
        )
    
    return True


# ============================================================================
# System Information Collection
# ============================================================================

def get_cpu_model() -> str:
    """Extract CPU model name from system"""
    if platform.system() == "Linux":
        try:
            with open('/proc/cpuinfo') as f:
                for line in f:
                    if line.startswith('model name'):
                        return line.split(':')[1].strip()
        except:
            pass
    elif platform.system() == "Darwin":  # macOS
        try:
            import subprocess
            result = subprocess.run(
                ['sysctl', '-n', 'machdep.cpu.brand_string'],
                capture_output=True, text=True
            )
            return result.stdout.strip()
        except:
            pass
    return "Unknown"


def collect_system_info() -> Dict[str, Any]:
    """
    Collect system and environment information for reproducibility
    
    Returns:
        Dictionary with CPU, memory, library versions, etc.
    """
    info = {
        # Platform
        'platform': platform.platform(),
        'python_version': platform.python_version(),
        'architecture': platform.machine(),
        
        # CPU
        'cpu_model': get_cpu_model(),
        
        # Memory
        'memory_total_gb': 'N/A',  # Requires psutil
        
        # Libraries
        'numpy_version': np.__version__,
        
        # Environment
        'timestamp': datetime.datetime.now().isoformat(),
        'hostname': platform.node(),
    }
    
    # Optional: Add psutil info if available
    try:
        import psutil
        info['cpu_cores_physical'] = psutil.cpu_count(logical=False)
        info['cpu_cores_logical'] = psutil.cpu_count(logical=True)
        if psutil.cpu_freq():
            info['cpu_freq_mhz'] = psutil.cpu_freq().current
        info['memory_total_gb'] = psutil.virtual_memory().total / (1024**3)
        info['memory_available_gb'] = psutil.virtual_memory().available / (1024**3)
    except ImportError:
        pass
    
    # Optional: Add torch info if available
    try:
        import torch
        info['torch_version'] = torch.__version__
        info['torch_num_threads'] = torch.get_num_threads()
    except ImportError:
        pass
    
    # Optional: Add hologram info if available
    try:
        import hologram as hg
        info['hologram_version'] = hg.__version__
    except (ImportError, AttributeError):
        pass
    
    return info


# ============================================================================
# Comparison and Formatting
# ============================================================================

def compare_results(
    result_a: BenchmarkResult,
    result_b: BenchmarkResult,
    label_a: str = "A",
    label_b: str = "B"
) -> Dict[str, Any]:
    """
    Compare two benchmark results and compute speedup
    
    Args:
        result_a: First benchmark result
        result_b: Second benchmark result
        label_a: Label for first result (default "A")
        label_b: Label for second result (default "B")
    
    Returns:
        Dictionary with comparison metrics
    """
    speedup = result_a.mean_ms / result_b.mean_ms
    
    return {
        'name': result_a.name,
        f'{label_a}_mean_ms': result_a.mean_ms,
        f'{label_a}_std_ms': result_a.std_ms,
        f'{label_a}_reliable': result_a.is_reliable,
        f'{label_b}_mean_ms': result_b.mean_ms,
        f'{label_b}_std_ms': result_b.std_ms,
        f'{label_b}_reliable': result_b.is_reliable,
        'speedup': speedup,
        'winner': label_b if speedup > 1.0 else label_a
    }


def format_benchmark_table(results: List[BenchmarkResult]) -> str:
    """
    Format benchmark results as a pretty table
    
    Args:
        results: List of BenchmarkResult objects
    
    Returns:
        Formatted string table
    """
    lines = []
    lines.append("-" * 80)
    lines.append(f"{'Operation':<30} {'Framework':<10} {'Mean (ms)':<12} {'Std (ms)':<12} {'Reliable':<10}")
    lines.append("-" * 80)
    
    for result in results:
        lines.append(
            f"{result.name:<30} "
            f"{result.framework:<10} "
            f"{result.mean_ms:>10.3f}  "
            f"{result.std_ms:>10.3f}  "
            f"{'✓' if result.is_reliable else '✗':<10}"
        )
    
    lines.append("-" * 80)
    return "\n".join(lines)


# ============================================================================
# Data Persistence
# ============================================================================

def save_results(
    results: List[BenchmarkResult],
    filepath: str,
    include_system_info: bool = True
) -> None:
    """
    Save benchmark results to JSON file
    
    Args:
        results: List of BenchmarkResult objects
        filepath: Output file path
        include_system_info: Include system information in output
    """
    data = {
        'results': [r.to_dict() for r in results],
        'version': __version__,
    }
    
    if include_system_info:
        data['system_info'] = collect_system_info()
    
    with open(filepath, 'w') as f:
        json.dump(data, f, indent=2)
    
    print(f"Saved {len(results)} results to {filepath}")


def load_results(filepath: str) -> List[BenchmarkResult]:
    """
    Load benchmark results from JSON file
    
    Args:
        filepath: Path to saved results
    
    Returns:
        List of BenchmarkResult objects
    """
    with open(filepath) as f:
        data = json.load(f)
    
    results = [BenchmarkResult(**r) for r in data['results']]
    print(f"Loaded {len(results)} results from {filepath}")
    
    return results


# ============================================================================
# Visualization (requires matplotlib)
# ============================================================================

def plot_comparison(
    results_pytorch: List[BenchmarkResult],
    results_atlas: List[BenchmarkResult],
    operation_name: str,
    save_path: Optional[str] = None
):
    """
    Plot side-by-side bar chart comparing PyTorch and Atlas
    
    Args:
        results_pytorch: List of PyTorch benchmark results
        results_atlas: List of Atlas benchmark results
        operation_name: Operation name for title
        save_path: Optional path to save figure
    
    Returns:
        Matplotlib figure
    """
    try:
        import matplotlib.pyplot as plt
    except ImportError:
        print("matplotlib not available, skipping plot")
        return None
    
    # Extract data
    sizes_pt = [r.size for r in results_pytorch]
    means_pt = [r.mean_ms for r in results_pytorch]
    stds_pt = [r.std_ms for r in results_pytorch]
    
    sizes_atlas = [r.size for r in results_atlas]
    means_atlas = [r.mean_ms for r in results_atlas]
    stds_atlas = [r.std_ms for r in results_atlas]
    
    # Create plot
    fig, ax = plt.subplots(figsize=(10, 6))
    
    x = np.arange(len(sizes_pt))
    width = 0.35
    
    ax.bar(x - width/2, means_pt, width, label='PyTorch CPU',
           yerr=stds_pt, capsize=5, color='#FF6B6B')
    ax.bar(x + width/2, means_atlas, width, label='Atlas',
           yerr=stds_atlas, capsize=5, color='#4ECDC4')
    
    ax.set_ylabel('Time (ms)')
    ax.set_title(f'{operation_name}: PyTorch vs Atlas')
    ax.set_xticks(x)
    ax.set_xticklabels([f"{s:,}" for s in sizes_pt])
    ax.set_xlabel('Input Size')
    ax.legend()
    ax.grid(axis='y', alpha=0.3)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved plot to {save_path}")
    
    return fig


def plot_speedup(
    results_pytorch: List[BenchmarkResult],
    results_atlas: List[BenchmarkResult],
    save_path: Optional[str] = None
):
    """
    Plot speedup chart (PyTorch time / Atlas time)
    
    Speedup > 1.0 means Atlas is faster
    Speedup < 1.0 means PyTorch is faster
    
    Args:
        results_pytorch: List of PyTorch benchmark results
        results_atlas: List of Atlas benchmark results  
        save_path: Optional path to save figure
    
    Returns:
        Matplotlib figure
    """
    try:
        import matplotlib.pyplot as plt
    except ImportError:
        print("matplotlib not available, skipping plot")
        return None
    
    # Group by operation and compute speedup
    operations = list(set(r.name for r in results_pytorch))
    speedups = []
    
    for op in operations:
        pt_results = [r for r in results_pytorch if r.name == op]
        atlas_results = [r for r in results_atlas if r.name == op]
        
        if pt_results and atlas_results:
            # Average speedup across sizes
            avg_speedup = np.mean([
                pt.mean_ms / atlas.mean_ms 
                for pt, atlas in zip(pt_results, atlas_results)
            ])
            speedups.append(avg_speedup)
        else:
            speedups.append(0.0)
    
    # Create plot
    fig, ax = plt.subplots(figsize=(12, 8))
    
    y_pos = np.arange(len(operations))
    colors = ['green' if s > 1.0 else 'red' for s in speedups]
    
    ax.barh(y_pos, speedups, color=colors, alpha=0.7)
    ax.set_yticks(y_pos)
    ax.set_yticklabels(operations)
    ax.set_xlabel('Speedup (PyTorch / Atlas)')
    ax.set_title('Performance Comparison: Speedup Factor')
    ax.axvline(x=1.0, color='black', linestyle='--', linewidth=2, label='Equal Performance')
    ax.legend()
    ax.grid(axis='x', alpha=0.3)
    
    # Add value labels
    for i, (op, speedup) in enumerate(zip(operations, speedups)):
        label = f"{speedup:.2f}x"
        x_pos = speedup + 0.05 if speedup > 1.0 else speedup - 0.05
        ha = 'left' if speedup > 1.0 else 'right'
        ax.text(x_pos, i, label, va='center', ha=ha, fontweight='bold')
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"Saved plot to {save_path}")
    
    return fig


# ============================================================================
# Usage Example (documentation)
# ============================================================================

USAGE_EXAMPLE = """
# Example Usage:

import numpy as np
import torch
import hologram as hg
from benchmark_utils import benchmark_operation, verify_correctness, plot_comparison

# Setup
exec = hg.Executor()
data = np.random.randn(10000).astype(np.float32)

# PyTorch version
def pytorch_add(a, b):
    return torch.add(a, b)

# Atlas version  
def atlas_add(a, b):
    return hg.ops.vector_add(a, b)

# Benchmark PyTorch
pytorch_result = benchmark_operation(
    pytorch_add,
    torch.from_numpy(data),
    torch.from_numpy(data),
    name="vector_add",
    framework="pytorch",
    size=len(data)
)

# Benchmark Atlas
atlas_result = benchmark_operation(
    atlas_add,
    exec.from_numpy(data),
    exec.from_numpy(data),
    name="vector_add",
    framework="atlas",
    size=len(data)
)

# Print results
print(f"PyTorch: {pytorch_result.mean_ms:.3f} ± {pytorch_result.std_ms:.3f} ms")
print(f"Atlas: {atlas_result.mean_ms:.3f} ± {atlas_result.std_ms:.3f} ms")
print(f"Speedup: {pytorch_result.mean_ms / atlas_result.mean_ms:.2f}x")

# Plot comparison
plot_comparison([pytorch_result], [atlas_result], "vector_add")
"""

if __name__ == "__main__":
    print(__doc__)
    print(USAGE_EXAMPLE)
