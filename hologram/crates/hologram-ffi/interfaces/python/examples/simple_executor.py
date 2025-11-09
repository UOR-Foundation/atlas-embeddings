#!/usr/bin/env python3
"""
Simple Executor Example

This example demonstrates basic executor operations without problematic features:
- Creating executors
- Basic buffer allocation
- Simple operations
- Proper cleanup
"""

import hologram_ffi as hg
import json

def main():
    print("=" * 60)
    print("Hologram FFI - Simple Executor Example")
    print("=" * 60)
    
    # Create executor
    print("\n🏗️ Creating Executor:")
    try:
        executor_handle = hg.new_executor()
        print(f"✅ Created executor with handle: {executor_handle}")
    except Exception as e:
        print(f"❌ Failed to create executor: {e}")
        return
    
    # Test basic buffer allocation
    print("\n📦 Buffer Allocation:")
    try:
        # Linear buffer only (avoid boundary buffers for now)
        linear_buffer_handle = hg.executor_allocate_buffer(executor_handle, 1000)
        print(f"✅ Allocated linear buffer: {linear_buffer_handle}")
        
    except Exception as e:
        print(f"❌ Buffer allocation failed: {e}")
        hg.executor_cleanup(executor_handle)
        return
    
    # Test basic buffer operations
    print("\n⚙️ Buffer Operations:")
    try:
        # Get buffer properties
        length = hg.buffer_length(linear_buffer_handle)
        print(f"✅ Buffer length: {length}")
        
        # Fill buffer
        hg.buffer_fill(linear_buffer_handle, 42.0, 1000)
        print("✅ Filled buffer with value 42.0")
        
        # Convert to vector (first few elements)
        data = hg.buffer_to_vec(linear_buffer_handle)
        print(f"✅ Buffer data (first 5 elements): {data[:5]}")
        
    except Exception as e:
        print(f"❌ Buffer operations failed: {e}")
    
    # Test Atlas state (independent of executor)
    print("\n🌐 Atlas State Management:")
    try:
        phase = hg.atlas_phase()
        print(f"✅ Atlas phase: {phase}")
        
        resonance = hg.atlas_resonance_at(0)
        print(f"✅ Atlas resonance at class 0: {resonance}")
        
        snapshot = hg.atlas_resonance_snapshot()
        snapshot_data = json.loads(snapshot)
        print(f"✅ Atlas resonance snapshot: {len(snapshot_data)} classes")
        
    except Exception as e:
        print(f"❌ Atlas state management failed: {e}")
    
    # Cleanup
    print("\n🧹 Cleanup:")
    try:
        hg.buffer_cleanup(linear_buffer_handle)
        hg.executor_cleanup(executor_handle)
        print("✅ All resources cleaned up successfully")
    except Exception as e:
        print(f"❌ Cleanup failed: {e}")
    
    print("\n✅ Simple executor example completed!")

if __name__ == "__main__":
    main()
