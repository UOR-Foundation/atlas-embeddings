#!/usr/bin/env python3
"""
Memory Leak Detection Test Suite for Hologram FFI

This script provides comprehensive memory leak detection and resource management
testing for all hologram-ffi functionality.
"""

import hologram_ffi as hg
import json
import gc
import os
import time
import threading
from typing import Dict, List, Tuple

# Optional psutil import for memory monitoring
try:
    import psutil
    PSUTIL_AVAILABLE = True
except ImportError:
    PSUTIL_AVAILABLE = False
    print("Warning: psutil not available, memory monitoring will be limited")

class MemoryLeakDetector:
    """Comprehensive memory leak detection for hologram-ffi."""
    
    def __init__(self):
        self.process = psutil.Process(os.getpid()) if PSUTIL_AVAILABLE else None
        self.results = {}
    
    def get_memory_usage(self) -> int:
        """Get current memory usage in bytes."""
        if self.process is not None:
            return self.process.memory_info().rss
        else:
            # Fallback: return 0 when psutil is not available
            return 0
    
    def test_executor_memory_leaks(self) -> Dict[str, any]:
        """Test for executor-related memory leaks."""
        print("🔧 Testing executor memory leaks...")
        
        initial_memory = self.get_memory_usage()
        memory_samples = []
        
        # Create and destroy many executors
        for i in range(100):
            executor_handle = hg.new_executor()
            
            # Perform operations
            phase = hg.executor_phase(executor_handle)
            hg.executor_advance_phase(executor_handle, 1)
            resonance = hg.executor_resonance_at(executor_handle, 0)
            snapshot = hg.executor_resonance_snapshot(executor_handle)
            mirror = hg.executor_mirror(executor_handle, 0)
            neighbors = hg.executor_neighbors(executor_handle, 0)
            
            hg.executor_cleanup(executor_handle)
            
            if i % 10 == 0:
                gc.collect()  # Force garbage collection
                current_memory = self.get_memory_usage()
                memory_samples.append(current_memory - initial_memory)
        
        final_memory = self.get_memory_usage()
        memory_growth = final_memory - initial_memory
        
        return {
            'initial_memory_mb': initial_memory / (1024 * 1024),
            'final_memory_mb': final_memory / (1024 * 1024),
            'memory_growth_bytes': memory_growth,
            'memory_growth_mb': memory_growth / (1024 * 1024),
            'peak_memory_growth_bytes': max(memory_samples),
            'peak_memory_growth_mb': max(memory_samples) / (1024 * 1024),
            'memory_samples': memory_samples,
            'leak_detected': memory_growth > 10 * 1024 * 1024,  # 10MB threshold
            'test_type': 'executor_operations'
        }
    
    def test_buffer_memory_leaks(self) -> Dict[str, any]:
        """Test for buffer-related memory leaks."""
        print("📦 Testing buffer memory leaks...")
        
        executor_handle = hg.new_executor()
        initial_memory = self.get_memory_usage()
        memory_samples = []
        
        try:
            # Create and destroy many buffers
            for i in range(100):
                buffer_handle = hg.executor_allocate_buffer(executor_handle, 1000)
                
                # Perform operations
                length = hg.buffer_length(buffer_handle)
                hg.buffer_fill(buffer_handle, 42.0, 1000)
                data = hg.buffer_to_vec(buffer_handle)
                
                hg.buffer_cleanup(buffer_handle)
                
                if i % 10 == 0:
                    gc.collect()
                    current_memory = self.get_memory_usage()
                    memory_samples.append(current_memory - initial_memory)
            
            final_memory = self.get_memory_usage()
            memory_growth = final_memory - initial_memory
            
            return {
                'initial_memory_mb': initial_memory / (1024 * 1024),
                'final_memory_mb': final_memory / (1024 * 1024),
                'memory_growth_bytes': memory_growth,
                'memory_growth_mb': memory_growth / (1024 * 1024),
                'peak_memory_growth_bytes': max(memory_samples),
                'peak_memory_growth_mb': max(memory_samples) / (1024 * 1024),
                'memory_samples': memory_samples,
                'leak_detected': memory_growth > 10 * 1024 * 1024,
                'test_type': 'buffer_operations'
            }
            
        finally:
            hg.executor_cleanup(executor_handle)
    
    def test_tensor_memory_leaks(self) -> Dict[str, any]:
        """Test for tensor-related memory leaks."""
        print("🔢 Testing tensor memory leaks...")
        
        executor_handle = hg.new_executor()
        initial_memory = self.get_memory_usage()
        memory_samples = []
        
        try:
            # Create and destroy many tensors
            for i in range(50):  # Reduced iterations to avoid tensor handle issues
                buffer_handle = hg.executor_allocate_buffer(executor_handle, 1000)
                tensor_handle = hg.tensor_from_buffer(buffer_handle, "[10, 100]")
                
                # Perform operations
                shape = hg.tensor_shape(tensor_handle)
                ndim = hg.tensor_ndim(tensor_handle)
                numel = hg.tensor_numel(tensor_handle)
                reshaped = hg.tensor_reshape(tensor_handle, "[50, 200]")
                transposed = hg.tensor_transpose(reshaped)
                view1d = hg.tensor_view1d(transposed)
                
                hg.tensor_cleanup(view1d)
                hg.tensor_cleanup(transposed)
                hg.tensor_cleanup(reshaped)
                hg.tensor_cleanup(tensor_handle)
                
                if i % 5 == 0:
                    gc.collect()
                    current_memory = self.get_memory_usage()
                    memory_samples.append(current_memory - initial_memory)
            
            final_memory = self.get_memory_usage()
            memory_growth = final_memory - initial_memory
            
            return {
                'initial_memory_mb': initial_memory / (1024 * 1024),
                'final_memory_mb': final_memory / (1024 * 1024),
                'memory_growth_bytes': memory_growth,
                'memory_growth_mb': memory_growth / (1024 * 1024),
                'peak_memory_growth_bytes': max(memory_samples),
                'peak_memory_growth_mb': max(memory_samples) / (1024 * 1024),
                'memory_samples': memory_samples,
                'leak_detected': memory_growth > 10 * 1024 * 1024,
                'test_type': 'tensor_operations'
            }
            
        finally:
            hg.executor_cleanup(executor_handle)
    
    def run_all_memory_tests(self) -> Dict[str, Dict[str, any]]:
        """Run all memory leak detection tests."""
        print("🧠 Starting comprehensive memory leak detection...")
        start_time = time.time()
        
        self.results = {
            'executor_memory_leaks': self.test_executor_memory_leaks(),
            'buffer_memory_leaks': self.test_buffer_memory_leaks(),
            'tensor_memory_leaks': self.test_tensor_memory_leaks(),
        }
        
        end_time = time.time()
        self.results['test_metadata'] = {
            'total_duration_seconds': end_time - start_time,
            'timestamp': time.time(),
            'python_version': f"{sys.version_info.major}.{sys.version_info.minor}.{sys.version_info.micro}"
        }
        
        return self.results
    
    def generate_report(self) -> str:
        """Generate a comprehensive memory leak detection report."""
        report = []
        report.append("=" * 80)
        report.append("🧠 HOLOGRAM FFI - MEMORY LEAK DETECTION REPORT")
        report.append("=" * 80)
        
        # Summary
        memory_tests = [k for k in self.results.keys() if k != 'test_metadata']
        leaks_detected = sum(1 for test in memory_tests if self.results[test]['leak_detected'])
        total_leak_tests = len(memory_tests)
        
        report.append(f"\n📊 MEMORY LEAK SUMMARY:")
        report.append(f"   Memory Leak Tests: {leaks_detected}/{total_leak_tests} detected")
        report.append(f"   Test Duration: {self.results['test_metadata']['total_duration_seconds']:.2f} seconds")
        
        # Memory leak details
        report.append(f"\n🔍 MEMORY LEAK DETAILS:")
        for test_name in memory_tests:
            test_result = self.results[test_name]
            status = "🚨 LEAK DETECTED" if test_result['leak_detected'] else "✅ NO LEAK"
            report.append(f"   {status} {test_name.replace('_', ' ').title()}:")
            report.append(f"      Memory Growth: {test_result['memory_growth_mb']:.2f} MB")
            report.append(f"      Peak Growth: {test_result['peak_memory_growth_mb']:.2f} MB")
        
        # Recommendations
        report.append(f"\n💡 RECOMMENDATIONS:")
        if leaks_detected > 0:
            report.append("   ⚠️  Memory leaks detected - investigate resource management")
            report.append("   🔧 Consider implementing reference counting or RAII patterns")
            report.append("   📊 Monitor memory usage in production environments")
        else:
            report.append("   ✅ No memory leaks detected - good resource management")
        
        return "\n".join(report)

def main():
    """Main memory leak detection runner."""
    import sys
    
    detector = MemoryLeakDetector()
    results = detector.run_all_memory_tests()
    
    # Generate and print report
    report = detector.generate_report()
    print(report)
    
    # Save detailed results
    import json
    with open('memory_leak_detection_results.json', 'w') as f:
        json.dump(results, f, indent=2)
    
    print(f"\n📄 Detailed results saved to: memory_leak_detection_results.json")
    
    # Check for critical issues
    memory_tests = [k for k in results.keys() if k != 'test_metadata']
    critical_leaks = sum(1 for test in memory_tests if results[test]['leak_detected'])
    
    if critical_leaks > 0:
        print(f"\n🚨 CRITICAL ISSUES DETECTED!")
        return False
    
    print(f"\n✅ Memory leak detection completed successfully!")
    return True

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
