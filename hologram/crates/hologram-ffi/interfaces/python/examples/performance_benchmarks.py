#!/usr/bin/env python3
"""
Performance Benchmarks

This example demonstrates performance testing and benchmarking including:
- Memory allocation performance
- Buffer operation performance
- Tensor operation performance
- Atlas state management performance
- Performance comparison and analysis
"""

import hologram_ffi as hg
import json
import time
import statistics

def benchmark_executor_creation():
    """Benchmark executor creation performance."""
    print("\n🏗️ Benchmarking Executor Creation:")
    
    times = []
    for i in range(10):
        start_time = time.time()
        executor_handle = hg.new_executor()
        end_time = time.time()
        
        creation_time = (end_time - start_time) * 1000  # Convert to milliseconds
        times.append(creation_time)
        
        # Cleanup
        hg.executor_cleanup(executor_handle)
    
    avg_time = statistics.mean(times)
    min_time = min(times)
    max_time = max(times)
    std_time = statistics.stdev(times) if len(times) > 1 else 0
    
    print(f"  Average: {avg_time:.2f} ms")
    print(f"  Min: {min_time:.2f} ms")
    print(f"  Max: {max_time:.2f} ms")
    print(f"  Std Dev: {std_time:.2f} ms")
    
    return avg_time

def benchmark_buffer_operations():
    """Benchmark buffer operation performance."""
    print("\n📦 Benchmarking Buffer Operations:")
    
    executor_handle = hg.new_executor()
    
    try:
        # Benchmark buffer allocation
        allocation_times = []
        buffer_handles = []
        
        for i in range(100):
            start_time = time.time()
            buffer_handle = hg.executor_allocate_buffer(executor_handle, 1000)
            end_time = time.time()
            
            allocation_time = (end_time - start_time) * 1000
            allocation_times.append(allocation_time)
            buffer_handles.append(buffer_handle)
        
        avg_allocation = statistics.mean(allocation_times)
        print(f"  Buffer Allocation (1000 elements):")
        print(f"    Average: {avg_allocation:.2f} ms")
        
        # Benchmark buffer operations
        if buffer_handles:
            # Fill operation
            fill_times = []
            for buffer_handle in buffer_handles[:10]:  # Test first 10
                start_time = time.time()
                hg.buffer_fill(buffer_handle, 42.0, 1000)
                end_time = time.time()
                
                fill_time = (end_time - start_time) * 1000
                fill_times.append(fill_time)
            
            avg_fill = statistics.mean(fill_times)
            print(f"  Buffer Fill (1000 elements):")
            print(f"    Average: {avg_fill:.2f} ms")
            
            # Copy operation
            copy_times = []
            for i in range(10):
                if i + 1 < len(buffer_handles):
                    start_time = time.time()
                    hg.buffer_copy(buffer_handles[i], buffer_handles[i + 1], 1000)
                    end_time = time.time()
                    
                    copy_time = (end_time - start_time) * 1000
                    copy_times.append(copy_time)
            
            avg_copy = statistics.mean(copy_times)
            print(f"  Buffer Copy (1000 elements):")
            print(f"    Average: {avg_copy:.2f} ms")
        
        # Cleanup buffers
        for buffer_handle in buffer_handles:
            hg.buffer_cleanup(buffer_handle)
        
        return avg_allocation
        
    finally:
        hg.executor_cleanup(executor_handle)

def benchmark_tensor_operations():
    """Benchmark tensor operation performance."""
    print("\n📊 Benchmarking Tensor Operations:")
    
    executor_handle = hg.new_executor()
    
    try:
        # Benchmark tensor operations
        operations = [
            ("Reshape", lambda: _benchmark_tensor_reshape(executor_handle)),
            ("Transpose", lambda: _benchmark_tensor_transpose(executor_handle)),
            ("View 1D", lambda: _benchmark_tensor_view_1d(executor_handle)),
        ]
        
        for op_name, op_func in operations:
            try:
                avg_time = op_func()
                print(f"  {op_name}: {avg_time:.2f} ms")
            except Exception as e:
                print(f"  {op_name}: Failed - {e}")
        
    finally:
        hg.executor_cleanup(executor_handle)

def _benchmark_tensor_reshape(executor_handle):
    """Benchmark tensor reshape operation."""
    times = []
    for i in range(10):
        # Create fresh buffer and tensor for each iteration
        buffer_handle = hg.executor_allocate_buffer(executor_handle, 10000)  # 10K elements
        tensor_handle = hg.tensor_from_buffer(buffer_handle, json.dumps([100, 100]))  # 100x100 matrix
        
        start_time = time.time()
        result_handle = hg.tensor_reshape(tensor_handle, json.dumps([1000, 10]))
        end_time = time.time()
        
        op_time = (end_time - start_time) * 1000
        times.append(op_time)
        
        # Cleanup
        hg.tensor_cleanup(result_handle)
    
    return statistics.mean(times)

def _benchmark_tensor_transpose(executor_handle):
    """Benchmark tensor transpose operation."""
    times = []
    for i in range(10):
        # Create fresh buffer and tensor for each iteration
        buffer_handle = hg.executor_allocate_buffer(executor_handle, 10000)  # 10K elements
        tensor_handle = hg.tensor_from_buffer(buffer_handle, json.dumps([100, 100]))  # 100x100 matrix
        
        start_time = time.time()
        result_handle = hg.tensor_transpose(tensor_handle)
        end_time = time.time()
        
        op_time = (end_time - start_time) * 1000
        times.append(op_time)
        
        # Cleanup
        hg.tensor_cleanup(result_handle)
    
    return statistics.mean(times)

def _benchmark_tensor_view_1d(executor_handle):
    """Benchmark tensor view_1d operation."""
    times = []
    for i in range(10):
        # Create fresh buffer and tensor for each iteration
        buffer_handle = hg.executor_allocate_buffer(executor_handle, 10000)  # 10K elements
        tensor_handle = hg.tensor_from_buffer(buffer_handle, json.dumps([100, 100]))  # 100x100 matrix
        
        start_time = time.time()
        result_handle = hg.tensor_view_1d(tensor_handle)
        end_time = time.time()
        
        op_time = (end_time - start_time) * 1000
        times.append(op_time)
        
        # Cleanup
        hg.tensor_cleanup(result_handle)
    
    return statistics.mean(times)

def benchmark_atlas_operations():
    """Benchmark Atlas state management performance."""
    print("\n🌐 Benchmarking Atlas Operations:")
    
    # Benchmark phase operations
    phase_times = []
    for i in range(1000):
        start_time = time.time()
        phase = hg.atlas_phase()
        end_time = time.time()
        
        phase_time = (end_time - start_time) * 1000
        phase_times.append(phase_time)
    
    avg_phase = statistics.mean(phase_times)
    print(f"  Atlas Phase (1000 calls):")
    print(f"    Average: {avg_phase:.4f} ms")
    
    # Benchmark resonance operations
    resonance_times = []
    for i in range(100):
        start_time = time.time()
        resonance = hg.atlas_resonance_at(i % 96)  # Valid class range
        end_time = time.time()
        
        resonance_time = (end_time - start_time) * 1000
        resonance_times.append(resonance_time)
    
    avg_resonance = statistics.mean(resonance_times)
    print(f"  Atlas Resonance (100 calls):")
    print(f"    Average: {avg_resonance:.4f} ms")
    
    # Benchmark snapshot operation
    snapshot_times = []
    for i in range(10):
        start_time = time.time()
        snapshot = hg.atlas_resonance_snapshot()
        end_time = time.time()
        
        snapshot_time = (end_time - start_time) * 1000
        snapshot_times.append(snapshot_time)
    
    avg_snapshot = statistics.mean(snapshot_times)
    print(f"  Atlas Snapshot (10 calls):")
    print(f"    Average: {avg_snapshot:.2f} ms")
    
    return avg_phase, avg_resonance, avg_snapshot

def benchmark_memory_usage():
    """Benchmark memory usage patterns."""
    print("\n💾 Benchmarking Memory Usage:")
    
    executor_handle = hg.new_executor()
    
    try:
        # Test memory allocation patterns
        buffer_sizes = [100, 1000, 10000, 100000]
        
        for size in buffer_sizes:
            times = []
            handles = []
            
            # Allocate multiple buffers of same size
            for i in range(5):
                start_time = time.time()
                buffer_handle = hg.executor_allocate_buffer(executor_handle, size)
                end_time = time.time()
                
                allocation_time = (end_time - start_time) * 1000
                times.append(allocation_time)
                handles.append(buffer_handle)
            
            avg_time = statistics.mean(times)
            print(f"  Buffer Size {size}: {avg_time:.2f} ms average")
            
            # Cleanup
            for handle in handles:
                hg.buffer_cleanup(handle)
        
    finally:
        hg.executor_cleanup(executor_handle)

def main():
    print("=" * 60)
    print("Hologram FFI - Performance Benchmarks")
    print("=" * 60)
    
    try:
        # Run all benchmarks
        executor_time = benchmark_executor_creation()
        buffer_time = benchmark_buffer_operations()
        benchmark_tensor_operations()
        atlas_times = benchmark_atlas_operations()
        benchmark_memory_usage()
        
        # Summary
        print("\n📊 Performance Summary:")
        print(f"  Executor Creation: {executor_time:.2f} ms")
        print(f"  Buffer Allocation: {buffer_time:.2f} ms")
        print(f"  Atlas Phase: {atlas_times[0]:.4f} ms")
        print(f"  Atlas Resonance: {atlas_times[1]:.4f} ms")
        print(f"  Atlas Snapshot: {atlas_times[2]:.2f} ms")
        
        print("\n✅ Performance benchmarks completed!")
        
    except Exception as e:
        print(f"❌ Benchmark failed: {e}")

if __name__ == "__main__":
    main()
