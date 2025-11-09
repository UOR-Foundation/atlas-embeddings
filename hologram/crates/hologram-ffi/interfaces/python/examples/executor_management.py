#!/usr/bin/env python3
"""
Executor Management Example

This example demonstrates comprehensive executor management including:
- Creating executors with different backends
- Buffer allocation (linear and boundary)
- Phase management
- Resonance tracking
- Topology operations (mirrors, neighbors)
- Proper cleanup
"""

import hologram_ffi as hg
import json

def main():
    print("=" * 60)
    print("Hologram FFI - Executor Management Example")
    print("=" * 60)
    
    # Create executor
    print("\n🏗️ Creating Executor:")
    try:
        executor_handle = hg.new_executor()
        print(f"✅ Created executor with handle: {executor_handle}")
    except Exception as e:
        print(f"❌ Failed to create executor: {e}")
        return
    
    # Test executor with custom backend
    print("\n🔧 Testing Custom Backend:")
    try:
        custom_executor_handle = hg.executor_with_backend("cpu")
        print(f"✅ Created executor with custom backend: {custom_executor_handle}")
        hg.executor_cleanup(custom_executor_handle)
        print("✅ Cleaned up custom executor")
    except Exception as e:
        print(f"❌ Custom backend test failed: {e}")
    
    # Test buffer allocation
    print("\n📦 Buffer Allocation:")
    try:
        # Linear buffer
        linear_buffer_handle = hg.executor_allocate_buffer(executor_handle, 1024)
        print(f"✅ Allocated linear buffer: {linear_buffer_handle}")
        
        # Boundary buffer (may fail on some systems)
        try:
            boundary_buffer_handle = hg.executor_allocate_boundary_buffer(executor_handle, 0, 32, 32)
            print(f"✅ Allocated boundary buffer: {boundary_buffer_handle}")
        except Exception as e:
            print(f"⚠️ Boundary buffer allocation failed (expected on some systems): {e}")
            boundary_buffer_handle = None
        
    except Exception as e:
        print(f"❌ Buffer allocation failed: {e}")
        boundary_buffer_handle = None
    
    # Test phase management
    print("\n⏰ Phase Management:")
    try:
        current_phase = hg.executor_phase(executor_handle)
        print(f"Current phase: {current_phase}")
        
        hg.executor_advance_phase(executor_handle, 5)
        new_phase = hg.executor_phase(executor_handle)
        print(f"Phase after advancing by 5: {new_phase}")
        
    except Exception as e:
        print(f"❌ Phase management failed: {e}")
    
    # Test resonance tracking
    print("\n🌊 Resonance Tracking:")
    try:
        # Get resonance for specific class
        resonance_0 = hg.executor_resonance_at(executor_handle, 0)
        resonance_42 = hg.executor_resonance_at(executor_handle, 42)
        print(f"Resonance at class 0: {resonance_0}")
        print(f"Resonance at class 42: {resonance_42}")
        
        # Get full resonance snapshot
        snapshot = hg.executor_resonance_snapshot(executor_handle)
        snapshot_data = json.loads(snapshot)
        print(f"Resonance snapshot: {len(snapshot_data)} classes")
        
    except Exception as e:
        print(f"❌ Resonance tracking failed: {e}")
    
    # Test topology operations
    print("\n🔗 Topology Operations:")
    try:
        # Mirror operations
        mirror_0 = hg.executor_mirror(executor_handle, 0)
        mirror_42 = hg.executor_mirror(executor_handle, 42)
        print(f"Mirror of class 0: {mirror_0}")
        print(f"Mirror of class 42: {mirror_42}")
        
        # Neighbor operations
        neighbors_0 = hg.executor_neighbors(executor_handle, 0)
        neighbors_data = json.loads(neighbors_0)
        print(f"Neighbors of class 0: {neighbors_data}")
        
    except Exception as e:
        print(f"❌ Topology operations failed: {e}")
    
    # Cleanup
    print("\n🧹 Cleanup:")
    try:
        hg.buffer_cleanup(linear_buffer_handle)
        if boundary_buffer_handle is not None:
            hg.buffer_cleanup(boundary_buffer_handle)
        hg.executor_cleanup(executor_handle)
        print("✅ All resources cleaned up successfully")
    except Exception as e:
        print(f"❌ Cleanup failed: {e}")
    
    print("\n✅ Executor management example completed!")

if __name__ == "__main__":
    main()
