#!/usr/bin/env python3
"""
Centralized Test Runner for Hologram FFI

This script runs all tests across all implemented language interfaces:
- Rust tests (unit and integration)
- Python tests
- TypeScript tests

All tests are run from their respective interface directories.
"""

import subprocess
import sys
import os
import json
import time
from pathlib import Path

class CentralizedTestRunner:
    """Centralized test runner for all hologram-ffi interfaces."""
    
    def __init__(self):
        self.project_root = Path(__file__).parent.parent.parent
        self.results = {
            'rust_unit_tests': {'status': 'pending', 'details': {}},
            'rust_integration_tests': {'status': 'pending', 'details': {}},
            'python_tests': {'status': 'pending', 'details': {}},
            'typescript_tests': {'status': 'pending', 'details': {}},
            'performance_tests': {'status': 'pending', 'details': {}},
            'memory_tests': {'status': 'pending', 'details': {}},
            'cross_platform_tests': {'status': 'pending', 'details': {}},
        }
    
    def run_rust_unit_tests(self):
        """Run Rust unit tests."""
        print("🔧 Running Rust unit tests...")
        try:
            # Run unit tests
            unit_result = subprocess.run(
                ['cargo', 'test', '--test', 'unit_tests'],
                cwd=self.project_root,
                capture_output=True,
                text=True,
                timeout=300
            )
            
            # Run integration tests
            integration_result = subprocess.run(
                ['cargo', 'test', '--test', 'integration_tests'],
                cwd=self.project_root,
                capture_output=True,
                text=True,
                timeout=300
            )
            
            # Run compilation test
            compile_result = subprocess.run(
                ['cargo', 'test', '--test', 'compile_test'],
                cwd=self.project_root,
                capture_output=True,
                text=True,
                timeout=300
            )
            
            # Combine results
            combined_success = (unit_result.returncode == 0 and 
                              integration_result.returncode == 0 and 
                              compile_result.returncode == 0)
            combined_stdout = unit_result.stdout + "\n" + integration_result.stdout + "\n" + compile_result.stdout
            combined_stderr = unit_result.stderr + "\n" + integration_result.stderr + "\n" + compile_result.stderr
            
            result = subprocess.CompletedProcess(
                args=['cargo', 'test'],
                returncode=0 if combined_success else 1,
                stdout=combined_stdout,
                stderr=combined_stderr
            )
            
            self.results['rust_unit_tests'] = {
                'status': 'passed' if result.returncode == 0 else 'failed',
                'details': {
                    'returncode': result.returncode,
                    'stdout': result.stdout,
                    'stderr': result.stderr
                }
            }
            
            if result.returncode == 0:
                print("✅ Rust unit tests passed")
            else:
                print("❌ Rust unit tests failed")
                print(result.stderr)
                
        except subprocess.TimeoutExpired:
            self.results['rust_unit_tests'] = {
                'status': 'timeout',
                'details': {'error': 'Test execution timed out'}
            }
            print("⏰ Rust unit tests timed out")
        except Exception as e:
            self.results['rust_unit_tests'] = {
                'status': 'error',
                'details': {'error': str(e)}
            }
            print(f"💥 Rust unit tests error: {e}")
    
    def run_rust_integration_tests(self):
        """Run Rust integration tests."""
        print("🔗 Running Rust integration tests...")
        try:
            result = subprocess.run(
                ['cargo', 'test', '--test', 'integration_tests'],
                cwd=self.project_root,
                capture_output=True,
                text=True,
                timeout=300
            )
            
            self.results['rust_integration_tests'] = {
                'status': 'passed' if result.returncode == 0 else 'failed',
                'details': {
                    'returncode': result.returncode,
                    'stdout': result.stdout,
                    'stderr': result.stderr
                }
            }
            
            if result.returncode == 0:
                print("✅ Rust integration tests passed")
            else:
                print("❌ Rust integration tests failed")
                print(result.stderr)
                
        except subprocess.TimeoutExpired:
            self.results['rust_integration_tests'] = {
                'status': 'timeout',
                'details': {'error': 'Test execution timed out'}
            }
            print("⏰ Rust integration tests timed out")
        except Exception as e:
            self.results['rust_integration_tests'] = {
                'status': 'error',
                'details': {'error': str(e)}
            }
            print(f"💥 Rust integration tests error: {e}")
    
    def run_python_tests(self):
        """Run Python tests from the Python interface directory."""
        print("🐍 Running Python tests...")
        try:
            python_test_dir = self.project_root / 'interfaces' / 'python'
            
            # Try to install pytest if not available
            try:
                subprocess.run([sys.executable, '-c', 'import pytest'], check=True, capture_output=True)
            except subprocess.CalledProcessError:
                print("Installing pytest...")
                subprocess.run([sys.executable, '-m', 'pip', 'install', 'pytest'], check=True)
            
            result = subprocess.run(
                [sys.executable, '-m', 'pytest', 'tests/', '-v', '--tb=short'],
                cwd=python_test_dir,
                capture_output=True,
                text=True,
                timeout=300
            )
            
            self.results['python_tests'] = {
                'status': 'passed' if result.returncode == 0 else 'failed',
                'details': {
                    'returncode': result.returncode,
                    'stdout': result.stdout,
                    'stderr': result.stderr
                }
            }
            
            if result.returncode == 0:
                print("✅ Python tests passed")
            else:
                print("❌ Python tests failed")
                print(result.stderr)
                
        except subprocess.TimeoutExpired:
            self.results['python_tests'] = {
                'status': 'timeout',
                'details': {'error': 'Test execution timed out'}
            }
            print("⏰ Python tests timed out")
        except Exception as e:
            self.results['python_tests'] = {
                'status': 'error',
                'details': {'error': str(e)}
            }
            print(f"💥 Python tests error: {e}")
    
    def run_typescript_tests(self):
        """Run TypeScript tests from the TypeScript interface directory."""
        print("📘 Running TypeScript tests...")
        try:
            typescript_test_dir = self.project_root / 'interfaces' / 'typescript'
            result = subprocess.run(
                ['npm', 'test'],
                cwd=typescript_test_dir,
                capture_output=True,
                text=True,
                timeout=300
            )
            
            self.results['typescript_tests'] = {
                'status': 'passed' if result.returncode == 0 else 'failed',
                'details': {
                    'returncode': result.returncode,
                    'stdout': result.stdout,
                    'stderr': result.stderr
                }
            }
            
            if result.returncode == 0:
                print("✅ TypeScript tests passed")
            else:
                print("❌ TypeScript tests failed")
                print(result.stderr)
                
        except subprocess.TimeoutExpired:
            self.results['typescript_tests'] = {
                'status': 'timeout',
                'details': {'error': 'Test execution timed out'}
            }
            print("⏰ TypeScript tests timed out")
        except Exception as e:
            self.results['typescript_tests'] = {
                'status': 'error',
                'details': {'error': str(e)}
            }
            print(f"💥 TypeScript tests error: {e}")
    
    def run_performance_tests(self):
        """Run performance benchmarks."""
        print("⚡ Running performance tests...")
        try:
            # Run Python performance benchmarks
            python_perf_dir = self.project_root / 'interfaces' / 'python' / 'examples'
            perf_result = subprocess.run(
                [sys.executable, 'performance_benchmarks.py'],
                cwd=python_perf_dir,
                capture_output=True,
                text=True,
                timeout=120
            )
            
            # Run TypeScript performance benchmarks
            typescript_perf_dir = self.project_root / 'interfaces' / 'typescript' / 'examples'
            ts_perf_result = subprocess.run(
                ['npx', 'ts-node', 'performance_benchmarks.ts'],
                cwd=typescript_perf_dir,
                capture_output=True,
                text=True,
                timeout=120
            )
            
            self.results['performance_tests'] = {
                'status': 'passed' if perf_result.returncode == 0 and ts_perf_result.returncode == 0 else 'failed',
                'details': {
                    'python_performance': {
                        'returncode': perf_result.returncode,
                        'stdout': perf_result.stdout,
                        'stderr': perf_result.stderr
                    },
                    'typescript_performance': {
                        'returncode': ts_perf_result.returncode,
                        'stdout': ts_perf_result.stdout,
                        'stderr': ts_perf_result.stderr
                    }
                }
            }
            
            if perf_result.returncode == 0 and ts_perf_result.returncode == 0:
                print("✅ Performance tests passed")
            else:
                print("❌ Performance tests failed")
                
        except Exception as e:
            self.results['performance_tests'] = {
                'status': 'error',
                'details': {'error': str(e)}
            }
            print(f"💥 Performance tests error: {e}")
    
    def run_memory_tests(self):
        """Run memory leak detection tests."""
        print("🧠 Running memory tests...")
        try:
            # Run Python memory tests
            python_test_dir = self.project_root / 'interfaces' / 'python' / 'tests'
            memory_test_script = """
import hologram_ffi as hg
import gc
import psutil
import os

def test_memory_leaks():
    process = psutil.Process(os.getpid())
    initial_memory = process.memory_info().rss
    
    # Create and destroy many resources
    for i in range(100):
        executor_handle = hg.new_executor()
        buffer_handle = hg.executor_allocate_buffer(executor_handle, 1000)
        tensor_handle = hg.tensor_from_buffer(buffer_handle, '[10, 100]')
        
        hg.tensor_cleanup(tensor_handle)
        hg.buffer_cleanup(buffer_handle)
        hg.executor_cleanup(executor_handle)
        
        if i % 10 == 0:
            gc.collect()
    
    final_memory = process.memory_info().rss
    memory_growth = final_memory - initial_memory
    
    print(f"Memory growth: {memory_growth} bytes")
    return memory_growth < 10 * 1024 * 1024  # Less than 10MB growth

if __name__ == "__main__":
    success = test_memory_leaks()
    exit(0 if success else 1)
"""
            
            # Write and run memory test
            memory_test_path = python_test_dir / 'memory_test.py'
            with open(memory_test_path, 'w') as f:
                f.write(memory_test_script)
            
            result = subprocess.run(
                [sys.executable, str(memory_test_path)],
                cwd=python_test_dir,
                capture_output=True,
                text=True,
                timeout=60
            )
            
            # Clean up
            memory_test_path.unlink()
            
            self.results['memory_tests'] = {
                'status': 'passed' if result.returncode == 0 else 'failed',
                'details': {
                    'returncode': result.returncode,
                    'stdout': result.stdout,
                    'stderr': result.stderr
                }
            }
            
            if result.returncode == 0:
                print("✅ Memory tests passed")
            else:
                print("❌ Memory tests failed")
                print(result.stderr)
                
        except Exception as e:
            self.results['memory_tests'] = {
                'status': 'error',
                'details': {'error': str(e)}
            }
            print(f"💥 Memory tests error: {e}")
    
    def run_cross_platform_tests(self):
        """Run cross-platform compatibility tests."""
        print("🌍 Running cross-platform tests...")
        try:
            # Run Python cross-platform tests
            python_test_dir = self.project_root / 'interfaces' / 'python' / 'tests'
            cross_platform_script = """
import hologram_ffi as hg
import platform
import sys

def test_cross_platform():
    tests_passed = 0
    total_tests = 0
    
    # Test basic functionality
    total_tests += 1
    try:
        version = hg.get_version()
        if version and len(version) > 0:
            tests_passed += 1
    except Exception:
        pass
    
    # Test executor operations
    total_tests += 1
    try:
        executor_handle = hg.new_executor()
        phase = hg.executor_phase(executor_handle)
        hg.executor_cleanup(executor_handle)
        if phase < 768:
            tests_passed += 1
    except Exception:
        pass
    
    # Test buffer operations
    total_tests += 1
    try:
        executor_handle = hg.new_executor()
        buffer_handle = hg.executor_allocate_buffer(executor_handle, 1000)
        length = hg.buffer_length(buffer_handle)
        hg.buffer_cleanup(buffer_handle)
        hg.executor_cleanup(executor_handle)
        if length == 1000:
            tests_passed += 1
    except Exception:
        pass
    
    print(f"Platform: {platform.platform()}")
    print(f"Python: {sys.version}")
    print(f"Tests passed: {tests_passed}/{total_tests}")
    return tests_passed == total_tests

if __name__ == "__main__":
    success = test_cross_platform()
    exit(0 if success else 1)
"""
            
            # Write and run cross-platform test
            cross_platform_path = python_test_dir / 'cross_platform_test.py'
            with open(cross_platform_path, 'w') as f:
                f.write(cross_platform_script)
            
            result = subprocess.run(
                [sys.executable, str(cross_platform_path)],
                cwd=python_test_dir,
                capture_output=True,
                text=True,
                timeout=60
            )
            
            # Clean up
            cross_platform_path.unlink()
            
            self.results['cross_platform_tests'] = {
                'status': 'passed' if result.returncode == 0 else 'failed',
                'details': {
                    'returncode': result.returncode,
                    'stdout': result.stdout,
                    'stderr': result.stderr
                }
            }
            
            if result.returncode == 0:
                print("✅ Cross-platform tests passed")
            else:
                print("❌ Cross-platform tests failed")
                print(result.stderr)
                
        except Exception as e:
            self.results['cross_platform_tests'] = {
                'status': 'error',
                'details': {'error': str(e)}
            }
            print(f"💥 Cross-platform tests error: {e}")
    
    def generate_report(self):
        """Generate comprehensive test report."""
        print("\n" + "="*80)
        print("🧪 HOLOGRAM FFI - CENTRALIZED TEST REPORT")
        print("="*80)
        
        total_tests = len(self.results)
        passed_tests = sum(1 for result in self.results.values() if result['status'] == 'passed')
        failed_tests = sum(1 for result in self.results.values() if result['status'] == 'failed')
        error_tests = sum(1 for result in self.results.values() if result['status'] == 'error')
        
        print(f"\n📊 SUMMARY:")
        print(f"   Total Test Suites: {total_tests}")
        print(f"   ✅ Passed: {passed_tests}")
        print(f"   ❌ Failed: {failed_tests}")
        print(f"   💥 Errors: {error_tests}")
        print(f"   Success Rate: {(passed_tests/total_tests)*100:.1f}%")
        
        print(f"\n📋 DETAILED RESULTS:")
        for test_name, result in self.results.items():
            status_emoji = {
                'passed': '✅',
                'failed': '❌',
                'error': '💥',
                'timeout': '⏰',
                'pending': '⏳'
            }.get(result['status'], '❓')
            
            print(f"   {status_emoji} {test_name.replace('_', ' ').title()}: {result['status']}")
            
            if result['status'] in ['failed', 'error'] and 'details' in result:
                if 'error' in result['details']:
                    print(f"      Error: {result['details']['error']}")
                elif 'stderr' in result['details'] and result['details']['stderr']:
                    print(f"      Error: {result['details']['stderr'][:100]}...")
        
        # Save detailed report
        report_path = self.project_root / 'test_report.json'
        with open(report_path, 'w') as f:
            json.dump(self.results, f, indent=2)
        
        print(f"\n📄 Detailed report saved to: {report_path}")
        
        return passed_tests == total_tests
    
    def run_all_tests(self):
        """Run all test suites."""
        print("🚀 Starting centralized test suite...")
        start_time = time.time()
        
        # Run all test categories
        self.run_rust_unit_tests()
        self.run_rust_integration_tests()
        self.run_python_tests()
        self.run_typescript_tests()
        self.run_performance_tests()
        self.run_memory_tests()
        self.run_cross_platform_tests()
        
        end_time = time.time()
        duration = end_time - start_time
        
        print(f"\n⏱️  Total test duration: {duration:.2f} seconds")
        
        # Generate report
        success = self.generate_report()
        
        return success

def main():
    """Main test runner entry point."""
    runner = CentralizedTestRunner()
    success = runner.run_all_tests()
    
    if success:
        print("\n🎉 ALL TESTS PASSED!")
        sys.exit(0)
    else:
        print("\n💥 SOME TESTS FAILED!")
        sys.exit(1)

if __name__ == "__main__":
    main()
