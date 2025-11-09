#!/usr/bin/env python3
"""
Error Handling Example

This example demonstrates comprehensive error handling patterns including:
- Graceful error handling for invalid operations
- Resource cleanup in error scenarios
- Error recovery strategies
- Best practices for FFI error handling
"""

import hologram_ffi as hg
import json

def safe_executor_operation():
    """Demonstrate safe executor operations with error handling."""
    executor_handle = None
    try:
        executor_handle = hg.new_executor()
        print(f"✅ Created executor: {executor_handle}")
        
        # Test valid operations
        phase = hg.executor_phase(executor_handle)
        print(f"✅ Got executor phase: {phase}")
        
        return executor_handle
        
    except Exception as e:
        print(f"❌ Executor operation failed: {e}")
        if executor_handle:
            try:
                hg.executor_cleanup(executor_handle)
            except:
                pass  # Ignore cleanup errors
        return None

def safe_buffer_operations(executor_handle):
    """Demonstrate safe buffer operations with error handling."""
    buffers = []
    
    try:
        # Create multiple buffers
        for i in range(3):
            buffer_handle = hg.executor_allocate_buffer(executor_handle, 100)
            buffers.append(buffer_handle)
            print(f"✅ Created buffer {i}: {buffer_handle}")
        
        # Test buffer operations
        if buffers:
            length = hg.buffer_length(buffers[0])
            print(f"✅ Buffer length: {length}")
            
            # Test invalid operation (this should fail gracefully)
            try:
                invalid_length = hg.buffer_length(99999)  # Invalid handle
                print(f"❌ Unexpected success with invalid handle: {invalid_length}")
            except Exception as e:
                print(f"✅ Correctly caught invalid buffer handle error: {type(e).__name__}")
        
        return buffers
        
    except Exception as e:
        print(f"❌ Buffer operations failed: {e}")
        # Cleanup any buffers that were created
        for buffer_handle in buffers:
            try:
                hg.buffer_cleanup(buffer_handle)
            except:
                pass
        return []

def safe_tensor_operations(executor_handle):
    """Demonstrate safe tensor operations with error handling."""
    tensors = []
    
    try:
        # Create buffer for tensor
        buffer_handle = hg.executor_allocate_buffer(executor_handle, 12)
        
        # Create tensor with valid shape
        valid_shape = [3, 4]
        tensor_handle = hg.tensor_from_buffer(buffer_handle, json.dumps(valid_shape))
        tensors.append(tensor_handle)
        print(f"✅ Created tensor with shape {valid_shape}: {tensor_handle}")
        
        # Test tensor operations
        shape = hg.tensor_shape(tensor_handle)
        print(f"✅ Tensor shape: {json.loads(shape)}")
        
        # Test invalid tensor operation
        try:
            invalid_tensor = hg.tensor_from_buffer(99999, json.dumps([2, 2]))  # Invalid buffer
            print(f"❌ Unexpected success with invalid buffer: {invalid_tensor}")
        except Exception as e:
            print(f"✅ Correctly caught invalid buffer error: {type(e).__name__}")
        
        # Test invalid reshape operation
        try:
            invalid_shape = [5, 5]  # Wrong number of elements
            reshaped = hg.tensor_reshape(tensor_handle, json.dumps(invalid_shape))
            print(f"❌ Unexpected success with invalid reshape: {reshaped}")
        except Exception as e:
            print(f"✅ Correctly caught invalid reshape error: {type(e).__name__}")
        
        return tensors
        
    except Exception as e:
        print(f"❌ Tensor operations failed: {e}")
        # Cleanup any tensors that were created
        for tensor_handle in tensors:
            try:
                hg.tensor_cleanup(tensor_handle)
            except:
                pass
        return []

def safe_atlas_operations():
    """Demonstrate safe Atlas state operations with error handling."""
    try:
        # Test valid Atlas operations
        phase = hg.atlas_phase()
        print(f"✅ Atlas phase: {phase}")
        
        resonance = hg.atlas_resonance_at(0)
        print(f"✅ Atlas resonance at class 0: {resonance}")
        
        # Test invalid class
        try:
            invalid_resonance = hg.atlas_resonance_at(200)  # Invalid class (>= 96)
            print(f"❌ Unexpected success with invalid class: {invalid_resonance}")
        except Exception as e:
            print(f"✅ Correctly caught invalid class error: {type(e).__name__}")
        
        # Test resonance snapshot
        snapshot = hg.atlas_resonance_snapshot()
        snapshot_data = json.loads(snapshot)
        print(f"✅ Atlas resonance snapshot: {len(snapshot_data)} classes")
        
    except Exception as e:
        print(f"❌ Atlas operations failed: {e}")

def cleanup_resources(executor_handle, buffers, tensors):
    """Demonstrate proper resource cleanup with error handling."""
    print("\n🧹 Cleaning up resources:")
    
    # Cleanup tensors
    for tensor_handle in tensors:
        try:
            hg.tensor_cleanup(tensor_handle)
            print(f"✅ Cleaned up tensor: {tensor_handle}")
        except Exception as e:
            print(f"⚠️ Failed to cleanup tensor {tensor_handle}: {e}")
    
    # Cleanup buffers
    for buffer_handle in buffers:
        try:
            hg.buffer_cleanup(buffer_handle)
            print(f"✅ Cleaned up buffer: {buffer_handle}")
        except Exception as e:
            print(f"⚠️ Failed to cleanup buffer {buffer_handle}: {e}")
    
    # Cleanup executor
    if executor_handle:
        try:
            hg.executor_cleanup(executor_handle)
            print(f"✅ Cleaned up executor: {executor_handle}")
        except Exception as e:
            print(f"⚠️ Failed to cleanup executor {executor_handle}: {e}")

def main():
    print("=" * 60)
    print("Hologram FFI - Error Handling Example")
    print("=" * 60)
    
    executor_handle = None
    buffers = []
    tensors = []
    
    try:
        # Test executor operations
        print("\n🏗️ Testing Executor Operations:")
        executor_handle = safe_executor_operation()
        
        if executor_handle:
            # Test buffer operations
            print("\n📦 Testing Buffer Operations:")
            buffers = safe_buffer_operations(executor_handle)
            
            # Test tensor operations
            print("\n📊 Testing Tensor Operations:")
            tensors = safe_tensor_operations(executor_handle)
        
        # Test Atlas operations (independent of executor)
        print("\n🌐 Testing Atlas Operations:")
        safe_atlas_operations()
        
    except Exception as e:
        print(f"❌ Unexpected error in main: {e}")
    
    finally:
        # Always cleanup resources
        cleanup_resources(executor_handle, buffers, tensors)
    
    print("\n✅ Error handling example completed!")

if __name__ == "__main__":
    main()
