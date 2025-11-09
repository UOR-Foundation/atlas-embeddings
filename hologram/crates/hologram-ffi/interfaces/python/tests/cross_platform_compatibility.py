#!/usr/bin/env python3
"""
Cross-Platform Compatibility Test Suite for Hologram FFI

This script tests hologram-ffi functionality across different platforms and
environments to ensure consistent behavior.
"""

import hologram_ffi as hg
import json
import platform
import sys
import os
import time
from typing import Dict, List, Any

class CrossPlatformTester:
    """Cross-platform compatibility testing for hologram-ffi."""
    
    def __init__(self):
        self.results = {}
        self.platform_info = self._get_platform_info()
    
    def _get_platform_info(self) -> Dict[str, str]:
        """Get detailed platform information."""
        return {
            'system': platform.system(),
            'release': platform.release(),
            'version': platform.version(),
            'machine': platform.machine(),
            'processor': platform.processor(),
            'python_version': f"{sys.version_info.major}.{sys.version_info.minor}.{sys.version_info.micro}",
            'python_implementation': platform.python_implementation(),
            'architecture': platform.architecture()[0],
            'platform': platform.platform()
        }
    
    def test_basic_functionality(self) -> Dict[str, Any]:
        """Test basic functionality across platforms."""
        print("🔧 Testing basic functionality...")
        
        tests = []
        
        # Test version
        try:
            version = hg.get_version()
            tests.append({
                'test': 'get_version',
                'success': True,
                'result': version,
                'error': None
            })
        except Exception as e:
            tests.append({
                'test': 'get_version',
                'success': False,
                'result': None,
                'error': str(e)
            })
        
        # Test Atlas phase
        try:
            phase = hg.atlas_phase()
            tests.append({
                'test': 'atlas_phase',
                'success': True,
                'result': phase,
                'error': None
            })
        except Exception as e:
            tests.append({
                'test': 'atlas_phase',
                'success': False,
                'result': None,
                'error': str(e)
            })
        
        # Test Atlas resonance
        try:
            resonance = hg.atlas_resonance_at(0)
            tests.append({
                'test': 'atlas_resonance_at',
                'success': True,
                'result': resonance,
                'error': None
            })
        except Exception as e:
            tests.append({
                'test': 'atlas_resonance_at',
                'success': False,
                'result': None,
                'error': str(e)
            })
        
        # Test Atlas snapshot
        try:
            snapshot = hg.atlas_resonance_snapshot()
            snapshot_data = json.loads(snapshot)
            tests.append({
                'test': 'atlas_resonance_snapshot',
                'success': True,
                'result': len(snapshot_data),
                'error': None
            })
        except Exception as e:
            tests.append({
                'test': 'atlas_resonance_snapshot',
                'success': False,
                'result': None,
                'error': str(e)
            })
        
        success_count = sum(1 for test in tests if test['success'])
        total_count = len(tests)
        
        return {
            'tests': tests,
            'success_rate': success_count / total_count,
            'success_count': success_count,
            'total_count': total_count,
            'platform_info': self.platform_info
        }
    
    def test_executor_compatibility(self) -> Dict[str, Any]:
        """Test executor functionality across platforms."""
        print("🔧 Testing executor compatibility...")
        
        tests = []
        
        try:
            # Test executor creation
            executor_handle = hg.new_executor()
            tests.append({
                'test': 'new_executor',
                'success': True,
                'result': executor_handle,
                'error': None
            })
            
            # Test executor operations
            phase = hg.executor_phase(executor_handle)
            tests.append({
                'test': 'executor_phase',
                'success': True,
                'result': phase,
                'error': None
            })
            
            hg.executor_advance_phase(executor_handle, 1)
            tests.append({
                'test': 'executor_advance_phase',
                'success': True,
                'result': None,
                'error': None
            })
            
            resonance = hg.executor_resonance_at(executor_handle, 0)
            tests.append({
                'test': 'executor_resonance_at',
                'success': True,
                'result': resonance,
                'error': None
            })
            
            snapshot = hg.executor_resonance_snapshot(executor_handle)
            tests.append({
                'test': 'executor_resonance_snapshot',
                'success': True,
                'result': len(json.loads(snapshot)),
                'error': None
            })
            
            mirror = hg.executor_mirror(executor_handle, 0)
            tests.append({
                'test': 'executor_mirror',
                'success': True,
                'result': mirror,
                'error': None
            })
            
            neighbors = hg.executor_neighbors(executor_handle, 0)
            tests.append({
                'test': 'executor_neighbors',
                'success': True,
                'result': len(json.loads(neighbors)),
                'error': None
            })
            
            # Test cleanup
            hg.executor_cleanup(executor_handle)
            tests.append({
                'test': 'executor_cleanup',
                'success': True,
                'result': None,
                'error': None
            })
            
        except Exception as e:
            tests.append({
                'test': 'executor_operations',
                'success': False,
                'result': None,
                'error': str(e)
            })
        
        success_count = sum(1 for test in tests if test['success'])
        total_count = len(tests)
        
        return {
            'tests': tests,
            'success_rate': success_count / total_count,
            'success_count': success_count,
            'total_count': total_count,
            'platform_info': self.platform_info
        }
    
    def test_buffer_compatibility(self) -> Dict[str, Any]:
        """Test buffer functionality across platforms."""
        print("📦 Testing buffer compatibility...")
        
        tests = []
        
        try:
            executor_handle = hg.new_executor()
            
            # Test buffer allocation
            buffer_handle = hg.executor_allocate_buffer(executor_handle, 1000)
            tests.append({
                'test': 'executor_allocate_buffer',
                'success': True,
                'result': buffer_handle,
                'error': None
            })
            
            # Test buffer properties
            length = hg.buffer_length(buffer_handle)
            tests.append({
                'test': 'buffer_length',
                'success': length == 1000,
                'result': length,
                'error': None if length == 1000 else f"Expected 1000, got {length}"
            })
            
            is_empty = hg.buffer_is_empty(buffer_handle)
            tests.append({
                'test': 'buffer_is_empty',
                'success': not is_empty,
                'result': is_empty,
                'error': None if not is_empty else "Buffer should not be empty"
            })
            
            is_linear = hg.buffer_is_linear(buffer_handle)
            tests.append({
                'test': 'buffer_is_linear',
                'success': is_linear,
                'result': is_linear,
                'error': None if is_linear else "Buffer should be linear"
            })
            
            element_size = hg.buffer_element_size(buffer_handle)
            tests.append({
                'test': 'buffer_element_size',
                'success': element_size == 4,
                'result': element_size,
                'error': None if element_size == 4 else f"Expected 4, got {element_size}"
            })
            
            size_bytes = hg.buffer_size_bytes(buffer_handle)
            tests.append({
                'test': 'buffer_size_bytes',
                'success': size_bytes == 4000,
                'result': size_bytes,
                'error': None if size_bytes == 4000 else f"Expected 4000, got {size_bytes}"
            })
            
            # Test buffer operations
            hg.buffer_fill(buffer_handle, 42.0, 1000)
            tests.append({
                'test': 'buffer_fill',
                'success': True,
                'result': None,
                'error': None
            })
            
            data = hg.buffer_to_vec(buffer_handle)
            data_vec = json.loads(data)
            tests.append({
                'test': 'buffer_to_vec',
                'success': len(data_vec) == 1000,
                'result': len(data_vec),
                'error': None if len(data_vec) == 1000 else f"Expected 1000 elements, got {len(data_vec)}"
            })
            
            # Test cleanup
            hg.buffer_cleanup(buffer_handle)
            tests.append({
                'test': 'buffer_cleanup',
                'success': True,
                'result': None,
                'error': None
            })
            
            hg.executor_cleanup(executor_handle)
            
        except Exception as e:
            tests.append({
                'test': 'buffer_operations',
                'success': False,
                'result': None,
                'error': str(e)
            })
        
        success_count = sum(1 for test in tests if test['success'])
        total_count = len(tests)
        
        return {
            'tests': tests,
            'success_rate': success_count / total_count,
            'success_count': success_count,
            'total_count': total_count,
            'platform_info': self.platform_info
        }
    
    def run_all_compatibility_tests(self) -> Dict[str, Dict[str, Any]]:
        """Run all cross-platform compatibility tests."""
        print("🌍 Starting cross-platform compatibility tests...")
        start_time = time.time()
        
        self.results = {
            'basic_functionality': self.test_basic_functionality(),
            'executor_compatibility': self.test_executor_compatibility(),
            'buffer_compatibility': self.test_buffer_compatibility(),
        }
        
        end_time = time.time()
        self.results['test_metadata'] = {
            'total_duration_seconds': end_time - start_time,
            'timestamp': time.time(),
            'platform_info': self.platform_info
        }
        
        return self.results
    
    def generate_report(self) -> str:
        """Generate a comprehensive compatibility report."""
        report = []
        report.append("=" * 80)
        report.append("🌍 HOLOGRAM FFI - CROSS-PLATFORM COMPATIBILITY REPORT")
        report.append("=" * 80)
        
        # Platform information
        report.append(f"\n🖥️  PLATFORM INFORMATION:")
        for key, value in self.platform_info.items():
            report.append(f"   {key.replace('_', ' ').title()}: {value}")
        
        # Summary
        test_categories = [k for k in self.results.keys() if k != 'test_metadata']
        total_tests = sum(self.results[cat]['total_count'] for cat in test_categories)
        total_successes = sum(self.results[cat]['success_count'] for cat in test_categories)
        overall_success_rate = total_successes / total_tests if total_tests > 0 else 0
        
        report.append(f"\n📊 COMPATIBILITY SUMMARY:")
        report.append(f"   Total Tests: {total_tests}")
        report.append(f"   Successful Tests: {total_successes}")
        report.append(f"   Success Rate: {overall_success_rate:.1%}")
        report.append(f"   Test Duration: {self.results['test_metadata']['total_duration_seconds']:.2f} seconds")
        
        # Detailed results
        report.append(f"\n📋 DETAILED RESULTS:")
        for category in test_categories:
            result = self.results[category]
            status = "✅ PASS" if result['success_rate'] >= 0.9 else "⚠️  PARTIAL" if result['success_rate'] >= 0.7 else "❌ FAIL"
            report.append(f"   {status} {category.replace('_', ' ').title()}: {result['success_count']}/{result['total_count']} ({result['success_rate']:.1%})")
            
            # Show failed tests
            failed_tests = [test for test in result['tests'] if not test['success']]
            if failed_tests:
                for test in failed_tests[:3]:  # Show first 3 failures
                    report.append(f"      ❌ {test['test']}: {test['error']}")
                if len(failed_tests) > 3:
                    report.append(f"      ... and {len(failed_tests) - 3} more failures")
        
        # Recommendations
        report.append(f"\n💡 RECOMMENDATIONS:")
        if overall_success_rate >= 0.95:
            report.append("   ✅ Excellent cross-platform compatibility")
            report.append("   🚀 Ready for production deployment")
        elif overall_success_rate >= 0.8:
            report.append("   ⚠️  Good compatibility with minor issues")
            report.append("   🔧 Address failing tests before production")
        else:
            report.append("   🚨 Significant compatibility issues detected")
            report.append("   🔧 Major fixes required before production")
            report.append("   📊 Consider platform-specific implementations")
        
        return "\n".join(report)

def main():
    """Main compatibility test runner."""
    import sys
    
    tester = CrossPlatformTester()
    results = tester.run_all_compatibility_tests()
    
    # Generate and print report
    report = tester.generate_report()
    print(report)
    
    # Save detailed results
    import json
    with open('cross_platform_compatibility_results.json', 'w') as f:
        json.dump(results, f, indent=2)
    
    print(f"\n📄 Detailed results saved to: cross_platform_compatibility_results.json")
    
    # Check overall success rate
    test_categories = [k for k in results.keys() if k != 'test_metadata']
    total_tests = sum(results[cat]['total_count'] for cat in test_categories)
    total_successes = sum(results[cat]['success_count'] for cat in test_categories)
    overall_success_rate = total_successes / total_tests if total_tests > 0 else 0
    
    if overall_success_rate >= 0.9:
        print(f"\n✅ Cross-platform compatibility tests passed!")
        return True
    else:
        print(f"\n❌ Cross-platform compatibility tests failed!")
        return False

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
