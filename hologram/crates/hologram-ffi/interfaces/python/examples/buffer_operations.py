#!/usr/bin/env python3
"""
Buffer Operations Example

This example demonstrates comprehensive buffer operations including:
- Buffer creation and management
- Buffer introspection (length, topology, properties)
- Buffer operations (copy, fill, data conversion)
- Memory management and cleanup
"""

import hologram_ffi as hg
import json

def main():
    print("=" * 60)
    print("Hologram FFI - Buffer Operations Example")
    print("=" * 60)
    
    # Create executor and buffers
    print("\n🏗️ Setting up Executor and Buffers:")
    try:
        executor_handle = hg.new_executor()
        print(f"✅ Created executor: {executor_handle}")
        
        # Create different types of buffers
        linear_buffer_handle = hg.executor_allocate_buffer(executor_handle, 1000)
        boundary_buffer_handle = hg.executor_allocate_boundary_buffer(executor_handle, 0, 16, 16)
        
        print(f"✅ Created linear buffer: {linear_buffer_handle}")
        print(f"✅ Created boundary buffer: {boundary_buffer_handle}")
        
    except Exception as e:
        print(f"❌ Setup failed: {e}")
        return
    
    # Buffer introspection
    print("\n🔍 Buffer Introspection:")
    try:
        # Linear buffer properties
        linear_length = hg.buffer_length(linear_buffer_handle)
        linear_backend_handle = hg.buffer_backend_handle(linear_buffer_handle)
        linear_topology = hg.buffer_topology(linear_buffer_handle)
        linear_is_empty = hg.buffer_is_empty(linear_buffer_handle)
        linear_pool = hg.buffer_pool(linear_buffer_handle)
        linear_is_linear = hg.buffer_is_linear(linear_buffer_handle)
        linear_is_boundary = hg.buffer_is_boundary(linear_buffer_handle)
        linear_element_size = hg.buffer_element_size(linear_buffer_handle)
        linear_size_bytes = hg.buffer_size_bytes(linear_buffer_handle)
        
        print(f"Linear Buffer Properties:")
        print(f"  Length: {linear_length}")
        print(f"  Backend Handle: {linear_backend_handle}")
        print(f"  Is Empty: {linear_is_empty}")
        print(f"  Pool: {linear_pool}")
        print(f"  Is Linear: {linear_is_linear}")
        print(f"  Is Boundary: {linear_is_boundary}")
        print(f"  Element Size: {linear_element_size}")
        print(f"  Size Bytes: {linear_size_bytes}")
        
        # Boundary buffer properties
        boundary_length = hg.buffer_length(boundary_buffer_handle)
        boundary_is_boundary = hg.buffer_is_boundary(boundary_buffer_handle)
        boundary_is_linear = hg.buffer_is_linear(boundary_buffer_handle)
        
        print(f"\nBoundary Buffer Properties:")
        print(f"  Length: {boundary_length}")
        print(f"  Is Boundary: {boundary_is_boundary}")
        print(f"  Is Linear: {boundary_is_linear}")
        
    except Exception as e:
        print(f"❌ Buffer introspection failed: {e}")
    
    # Buffer operations
    print("\n⚙️ Buffer Operations:")
    try:
        # Create source and destination buffers for copying
        src_buffer_handle = hg.executor_allocate_buffer(executor_handle, 100)
        dst_buffer_handle = hg.executor_allocate_buffer(executor_handle, 100)
        
        print(f"✅ Created source buffer: {src_buffer_handle}")
        print(f"✅ Created destination buffer: {dst_buffer_handle}")
        
        # Fill source buffer with test data
        test_data = [1.0, 2.0, 3.0, 4.0, 5.0] * 20  # 100 elements
        hg.buffer_copy_from_slice(src_buffer_handle, json.dumps(test_data))
        print("✅ Filled source buffer with test data")
        
        # Copy from source to destination
        hg.buffer_copy(src_buffer_handle, dst_buffer_handle, 100)
        print("✅ Copied data from source to destination")
        
        # Fill destination buffer with a constant value
        hg.buffer_fill(dst_buffer_handle, 42.0, 100)
        print("✅ Filled destination buffer with constant value")
        
        # Convert buffer to vector for inspection
        buffer_data = hg.buffer_to_vec(dst_buffer_handle)
        print(f"✅ Converted buffer to vector (first 5 elements): {buffer_data[:5]}")
        
        # Cleanup test buffers
        hg.buffer_cleanup(src_buffer_handle)
        hg.buffer_cleanup(dst_buffer_handle)
        
    except Exception as e:
        print(f"❌ Buffer operations failed: {e}")
    
    # Cleanup
    print("\n🧹 Cleanup:")
    try:
        hg.buffer_cleanup(linear_buffer_handle)
        hg.buffer_cleanup(boundary_buffer_handle)
        hg.executor_cleanup(executor_handle)
        print("✅ All resources cleaned up successfully")
    except Exception as e:
        print(f"❌ Cleanup failed: {e}")
    
    print("\n✅ Buffer operations example completed!")

if __name__ == "__main__":
    main()
