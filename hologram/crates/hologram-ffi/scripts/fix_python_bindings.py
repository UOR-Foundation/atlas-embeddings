#!/usr/bin/env python3
"""
Manual fix for Python PoisonError - copy library and regenerate bindings
"""

import subprocess
import sys
import os
import shutil

def fix_python_bindings():
    """Fix Python bindings by copying library and regenerating."""
    os.chdir('/workspace/crates/hologram-ffi')
    
    try:
        print("🔨 Building debug library...")
        result = subprocess.run(['cargo', 'build'], 
                               capture_output=True, text=True, timeout=120)
        
        if result.returncode != 0:
            print(f"❌ Build failed: {result.stderr}")
            return False
        
        print("✅ Library built successfully!")
        
        print("🔄 Generating Python bindings...")
        result = subprocess.run(['cargo', 'run', '--bin', 'generate-bindings'], 
                               capture_output=True, text=True, timeout=120)
        
        if result.returncode != 0:
            print(f"❌ Bindings generation failed: {result.stderr}")
            return False
        
        print("✅ Python bindings generated!")
        
        # Copy the generated library to Python package
        print("📦 Copying library to Python package...")
        src_lib = '/workspace/target/debug/libhologram_ffi.so'
        dst_lib = '/workspace/crates/hologram-ffi/interfaces/python/hologram_ffi/libuniffi_hologram_ffi.so'
        
        if os.path.exists(src_lib):
            shutil.copy2(src_lib, dst_lib)
            print("✅ Library copied successfully!")
        else:
            print(f"❌ Source library not found: {src_lib}")
            return False
        
        # Copy the generated Python bindings
        print("📦 Copying Python bindings...")
        src_py = '/workspace/crates/hologram-ffi/hologram_ffi.py'
        dst_py = '/workspace/crates/hologram-ffi/interfaces/python/hologram_ffi/hologram_ffi.py'
        
        if os.path.exists(src_py):
            shutil.copy2(src_py, dst_py)
            print("✅ Python bindings copied successfully!")
        else:
            print(f"❌ Source Python bindings not found: {src_py}")
            return False
        
        print("🎉 Python bindings fix completed successfully!")
        return True
        
    except subprocess.TimeoutExpired:
        print("⏰ Operation timed out")
        return False
    except Exception as e:
        print(f"💥 Error: {e}")
        return False

if __name__ == "__main__":
    success = fix_python_bindings()
    sys.exit(0 if success else 1)
