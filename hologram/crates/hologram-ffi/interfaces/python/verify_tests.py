#!/usr/bin/env python3
"""
Quick Test Verification Script

This script verifies that the test structure is properly set up and can be executed.
"""

import subprocess
import sys
from pathlib import Path

def test_structure():
    """Test that the test structure is properly set up."""
    project_root = Path(__file__).parent.parent.parent
    
    print("🔍 Verifying test structure...")
    
    # Check that test files exist
    test_files = [
        project_root / "scripts" / "run_tests.sh",
        project_root / "tests" / "unit_tests.rs",
        project_root / "tests" / "integration_tests.rs",
        project_root / "tests" / "compile_test.rs",
        project_root / "interfaces" / "python" / "tests" / "test_hologram_ffi.py",
        project_root / "interfaces" / "typescript" / "tests" / "hologram_ffi.test.ts",
        project_root / "tests" / "README.md"
    ]
    
    missing_files = []
    for file_path in test_files:
        if not file_path.exists():
            missing_files.append(str(file_path))
    
    if missing_files:
        print("❌ Missing test files:")
        for file_path in missing_files:
            print(f"   - {file_path}")
        return False
    
    print("✅ All test files present")
    
    # Check that Rust tests can be compiled
    print("🔧 Testing Rust compilation...")
    try:
        result = subprocess.run(
            ["cargo", "check", "--tests"],
            cwd=project_root,
            capture_output=True,
            text=True,
            timeout=60
        )
        
        if result.returncode == 0:
            print("✅ Rust tests compile successfully")
        else:
            print("❌ Rust compilation failed:")
            print(result.stderr)
            return False
            
    except subprocess.TimeoutExpired:
        print("⏰ Rust compilation timed out")
        return False
    except Exception as e:
        print(f"💥 Rust compilation error: {e}")
        return False
    
    # Check that Python tests can be imported
    print("🐍 Testing Python test imports...")
    try:
        python_test_dir = project_root / "interfaces" / "python"
        result = subprocess.run(
            [sys.executable, "-c", "import hologram_ffi; print('Import successful')"],
            cwd=python_test_dir,
            capture_output=True,
            text=True,
            timeout=30
        )
        
        if result.returncode == 0:
            print("✅ Python tests can import hologram_ffi")
        else:
            print("❌ Python import failed:")
            print(result.stderr)
            return False
            
    except Exception as e:
        print(f"💥 Python import error: {e}")
        return False
    
    # Check that TypeScript tests can be compiled
    print("📘 Testing TypeScript compilation...")
    try:
        typescript_test_dir = project_root / "interfaces" / "typescript"
        result = subprocess.run(
            ["npx", "tsc", "--noEmit"],
            cwd=typescript_test_dir,
            capture_output=True,
            text=True,
            timeout=60
        )
        
        if result.returncode == 0:
            print("✅ TypeScript tests compile successfully")
        else:
            print("❌ TypeScript compilation failed:")
            print(result.stderr)
            return False
            
    except subprocess.TimeoutExpired:
        print("⏰ TypeScript compilation timed out")
        return False
    except Exception as e:
        print(f"💥 TypeScript compilation error: {e}")
        return False
    
    print("\n🎉 Test structure verification completed successfully!")
    return True

def main():
    """Main verification function."""
    success = test_structure()
    
    if success:
        print("\n✅ All tests are ready to run!")
        print("Use './scripts/run_tests.sh' or 'python interfaces/python/run_tests.py' to run all tests")
        sys.exit(0)
    else:
        print("\n❌ Test structure verification failed!")
        sys.exit(1)

if __name__ == "__main__":
    main()
