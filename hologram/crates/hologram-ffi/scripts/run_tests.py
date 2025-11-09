#!/usr/bin/env python3
"""
Comprehensive test runner for hologram-ffi
Runs all tests across Rust, Python, and TypeScript interfaces
"""

import subprocess
import sys
import os
import time
import json
from pathlib import Path
from typing import Dict, List, Tuple, Optional
import argparse


class TestRunner:
    """Main test runner class for hologram-ffi"""
    
    def __init__(self, verbose: bool = False, coverage: bool = False):
        self.verbose = verbose
        self.coverage = coverage
        self.results: Dict[str, Dict] = {}
        self.start_time = time.time()
        
    def log(self, message: str, level: str = "INFO"):
        """Log messages with timestamps"""
        timestamp = time.strftime("%H:%M:%S")
        print(f"[{timestamp}] [{level}] {message}")
        
    def run_command(self, cmd: List[str], cwd: Optional[str] = None) -> Tuple[int, str, str]:
        """Run a command and return exit code, stdout, stderr"""
        try:
            result = subprocess.run(
                cmd, 
                cwd=cwd, 
                capture_output=True, 
                text=True, 
                timeout=300  # 5 minute timeout
            )
            return result.returncode, result.stdout, result.stderr
        except subprocess.TimeoutExpired:
            return -1, "", "Command timed out after 5 minutes"
        except Exception as e:
            return -1, "", str(e)
    
    def run_rust_tests(self) -> bool:
        """Run Rust unit tests"""
        self.log("Running Rust unit tests...")
        
        # Run unit tests
        cmd = ["cargo", "test", "--package", "hologram-ffi", "--test", "unit_tests"]
        exit_code, stdout, stderr = self.run_command(cmd)
        
        if exit_code == 0:
            # Parse test results
            lines = stdout.split('\n')
            test_count = 0
            passed = 0
            
            for line in lines:
                if "test result:" in line:
                    # Extract test counts
                    if "ok" in line:
                        parts = line.split()
                        for i, part in enumerate(parts):
                            if part.isdigit():
                                test_count = int(part)
                                break
                    break
            
            self.results["rust_tests"] = {
                "status": "PASSED",
                "test_count": test_count,
                "passed": test_count,
                "failed": 0,
                "duration": time.time() - self.start_time
            }
            
            self.log(f"Rust tests passed: {test_count}/{test_count}")
            return True
        else:
            self.results["rust_tests"] = {
                "status": "FAILED",
                "exit_code": exit_code,
                "stderr": stderr,
                "duration": time.time() - self.start_time
            }
            self.log(f"Rust tests failed: {stderr}", "ERROR")
            return False
    
    def run_python_tests(self) -> bool:
        """Run Python interface tests"""
        self.log("Running Python interface tests...")
        
        python_dir = Path("interfaces/python")
        if not python_dir.exists():
            self.log("Python interface directory not found", "ERROR")
            return False
            
        cmd = ["python", "-m", "pytest", "tests/test_hologram_ffi.py", "-v"]
        if self.coverage:
            cmd.extend(["--cov=hologram_ffi", "--cov-report=term-missing"])
            
        exit_code, stdout, stderr = self.run_command(cmd, cwd=str(python_dir))
        
        if exit_code == 0:
            # Parse pytest results
            lines = stdout.split('\n')
            test_count = 0
            passed = 0
            
            for line in lines:
                if "passed" in line and "failed" in line:
                    # Extract test counts from pytest output
                    parts = line.split()
                    for part in parts:
                        if part.isdigit():
                            test_count = int(part)
                            break
                    break
            
            self.results["python_tests"] = {
                "status": "PASSED",
                "test_count": test_count,
                "passed": test_count,
                "failed": 0,
                "duration": time.time() - self.start_time
            }
            
            self.log(f"Python tests passed: {test_count}/{test_count}")
            return True
        else:
            self.results["python_tests"] = {
                "status": "FAILED",
                "exit_code": exit_code,
                "stderr": stderr,
                "duration": time.time() - self.start_time
            }
            self.log(f"Python tests failed: {stderr}", "ERROR")
            return False
    
    def run_typescript_tests(self) -> bool:
        """Run TypeScript interface tests"""
        self.log("Running TypeScript interface tests...")
        
        typescript_dir = Path("interfaces/typescript")
        if not typescript_dir.exists():
            self.log("TypeScript interface directory not found", "ERROR")
            return False
            
        # Install dependencies if needed
        if not (typescript_dir / "node_modules").exists():
            self.log("Installing TypeScript dependencies...")
            install_cmd = ["npm", "install"]
            exit_code, _, stderr = self.run_command(install_cmd, cwd=str(typescript_dir))
            if exit_code != 0:
                self.log(f"Failed to install dependencies: {stderr}", "ERROR")
                return False
        
        # Run tests
        cmd = ["npm", "test"]
        if self.coverage:
            cmd = ["npm", "run", "test:coverage"]
            
        exit_code, stdout, stderr = self.run_command(cmd, cwd=str(typescript_dir))
        
        if exit_code == 0:
            # Parse test results
            lines = stdout.split('\n')
            test_count = 0
            passed = 0
            
            for line in lines:
                if "Tests:" in line or "test" in line.lower():
                    # Extract test counts from jest output
                    parts = line.split()
                    for part in parts:
                        if part.isdigit():
                            test_count = int(part)
                            break
                    break
            
            self.results["typescript_tests"] = {
                "status": "PASSED",
                "test_count": test_count,
                "passed": test_count,
                "failed": 0,
                "duration": time.time() - self.start_time
            }
            
            self.log(f"TypeScript tests passed: {test_count}/{test_count}")
            return True
        else:
            self.results["typescript_tests"] = {
                "status": "FAILED",
                "exit_code": exit_code,
                "stderr": stderr,
                "duration": time.time() - self.start_time
            }
            self.log(f"TypeScript tests failed: {stderr}", "ERROR")
            return False
    
    def run_performance_tests(self) -> bool:
        """Run performance benchmarks"""
        self.log("Running performance tests...")
        
        # Run Rust benchmarks
        cmd = ["cargo", "bench", "--package", "hologram-ffi"]
        exit_code, stdout, stderr = self.run_command(cmd)
        
        if exit_code == 0:
            self.results["performance_tests"] = {
                "status": "PASSED",
                "duration": time.time() - self.start_time
            }
            self.log("Performance tests passed")
            return True
        else:
            self.results["performance_tests"] = {
                "status": "FAILED",
                "exit_code": exit_code,
                "stderr": stderr,
                "duration": time.time() - self.start_time
            }
            self.log(f"Performance tests failed: {stderr}", "ERROR")
            return False
    
    def run_memory_tests(self) -> bool:
        """Run memory leak detection tests"""
        self.log("Running memory leak tests...")
        
        # Run Python memory tests
        python_dir = Path("interfaces/python")
        cmd = ["python", "-m", "pytest", "tests/test_hologram_ffi.py::TestMemoryManagement", "-v"]
        exit_code, stdout, stderr = self.run_command(cmd, cwd=str(python_dir))
        
        if exit_code == 0:
            self.results["memory_tests"] = {
                "status": "PASSED",
                "duration": time.time() - self.start_time
            }
            self.log("Memory tests passed")
            return True
        else:
            self.results["memory_tests"] = {
                "status": "FAILED",
                "exit_code": exit_code,
                "stderr": stderr,
                "duration": time.time() - self.start_time
            }
            self.log(f"Memory tests failed: {stderr}", "ERROR")
            return False
    
    def generate_report(self) -> Dict:
        """Generate comprehensive test report"""
        total_time = time.time() - self.start_time
        
        report = {
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
            "total_duration": total_time,
            "results": self.results,
            "summary": {
                "total_tests": 0,
                "passed_tests": 0,
                "failed_tests": 0,
                "success_rate": 0.0
            }
        }
        
        # Calculate summary
        for test_suite, result in self.results.items():
            if "test_count" in result:
                report["summary"]["total_tests"] += result["test_count"]
                if result["status"] == "PASSED":
                    report["summary"]["passed_tests"] += result["test_count"]
                else:
                    report["summary"]["failed_tests"] += result["test_count"]
        
        if report["summary"]["total_tests"] > 0:
            report["summary"]["success_rate"] = (
                report["summary"]["passed_tests"] / report["summary"]["total_tests"]
            ) * 100
        
        return report
    
    def run_all_tests(self) -> bool:
        """Run all test suites"""
        self.log("Starting comprehensive test suite...")
        
        test_suites = [
            ("Rust Tests", self.run_rust_tests),
            ("Python Tests", self.run_python_tests),
            ("TypeScript Tests", self.run_typescript_tests),
            ("Performance Tests", self.run_performance_tests),
            ("Memory Tests", self.run_memory_tests),
        ]
        
        all_passed = True
        
        for suite_name, test_func in test_suites:
            self.log(f"Running {suite_name}...")
            if not test_func():
                all_passed = False
        
        # Generate and save report
        report = self.generate_report()
        
        # Save report to file
        report_file = Path("test_report.json")
        with open(report_file, 'w') as f:
            json.dump(report, f, indent=2)
        
        self.log(f"Test report saved to {report_file}")
        
        # Print summary
        self.log("=" * 50)
        self.log("TEST SUMMARY")
        self.log("=" * 50)
        self.log(f"Total Tests: {report['summary']['total_tests']}")
        self.log(f"Passed: {report['summary']['passed_tests']}")
        self.log(f"Failed: {report['summary']['failed_tests']}")
        self.log(f"Success Rate: {report['summary']['success_rate']:.1f}%")
        self.log(f"Total Duration: {total_time:.2f}s")
        
        return all_passed


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(description="Run hologram-ffi test suite")
    parser.add_argument("-v", "--verbose", action="store_true", help="Verbose output")
    parser.add_argument("-c", "--coverage", action="store_true", help="Generate coverage reports")
    parser.add_argument("--rust-only", action="store_true", help="Run only Rust tests")
    parser.add_argument("--python-only", action="store_true", help="Run only Python tests")
    parser.add_argument("--typescript-only", action="store_true", help="Run only TypeScript tests")
    
    args = parser.parse_args()
    
    runner = TestRunner(verbose=args.verbose, coverage=args.coverage)
    
    if args.rust_only:
        success = runner.run_rust_tests()
    elif args.python_only:
        success = runner.run_python_tests()
    elif args.typescript_only:
        success = runner.run_typescript_tests()
    else:
        success = runner.run_all_tests()
    
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
