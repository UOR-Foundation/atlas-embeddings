#!/usr/bin/env python3
"""
Test if the lock_registry function is working by testing get_registry_status
"""

import sys
import os

# Add the Python package to the path
sys.path.insert(0, '/workspace/crates/hologram-ffi/interfaces/python')

try:
    import hologram_ffi as hg
    
    print("Testing if lock_registry function is working...")
    
    # Test if get_registry_status works (this uses lock_registry)
    try:
        status = hg.get_registry_status()
        print(f"✅ get_registry_status works: {status}")
        
        # Test if clear_all_registries works
        hg.clear_all_registries()
        print("✅ clear_all_registries works")
        
        # Test if we can create an executor now
        executor_handle = hg.new_executor()
        print(f"✅ new_executor works: {executor_handle}")
        
        # Clean up
        hg.executor_cleanup(executor_handle)
        print("✅ executor_cleanup works")
        
        print("🎉 All tests passed! The lock_registry function is working.")
        
    except AttributeError as e:
        print(f"❌ Function not available: {e}")
        print("The library needs to be rebuilt with the new functions.")
        
    except Exception as e:
        print(f"❌ Error: {e}")
        print("The library is using the old version without lock_registry.")
        
except ImportError as e:
    print(f"❌ Cannot import hologram_ffi: {e}")
    print("The Python package is not properly installed.")
