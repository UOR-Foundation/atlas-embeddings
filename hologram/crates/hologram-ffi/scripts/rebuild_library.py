#!/usr/bin/env python3
"""
Comprehensive rebuild script for hologram-ffi to fix PoisonError
"""

import subprocess
import sys
import os
import shutil
import time

def run_command(cmd, description, timeout=300):
    """Run a command with error handling."""
    print(f"🔄 {description}...")
    try:
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=timeout)
        if result.returncode == 0:
            print(f"✅ {description} completed successfully")
            return True
        else:
            print(f"❌ {description} failed:")
            print(f"STDOUT: {result.stdout}")
            print(f"STDERR: {result.stderr}")
            return False
    except subprocess.TimeoutExpired:
        print(f"⏰ {description} timed out")
        return False
    except Exception as e:
        print(f"💥 {description} error: {e}")
        return False

def rebuild_library():
    """Rebuild the library and regenerate Python bindings."""
    os.chdir('/workspace/crates/hologram-ffi')
    
    # Step 1: Clean previous build
    if not run_command('cargo clean', 'Cleaning previous build'):
        return False
    
    # Step 2: Build the library
    if not run_command('cargo build', 'Building library'):
        return False
    
    # Step 3: Generate bindings
    if not run_command('cargo run --bin generate-bindings', 'Generating bindings'):
        return False
    
    # Step 4: Install Python package
    os.chdir('/workspace/crates/hologram-ffi/interfaces/python')
    if not run_command('pip install -e . --force-reinstall', 'Installing Python package'):
        return False
    
    print("🎉 Library rebuild completed successfully!")
    return True

if __name__ == "__main__":
    success = rebuild_library()
    sys.exit(0 if success else 1)
