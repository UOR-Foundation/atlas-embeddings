#!/usr/bin/env python3
"""
Simple Tensor Example

This example demonstrates basic tensor operations without complex workflows:
- Tensor creation from buffers
- Basic tensor introspection
- Simple tensor operations
- Proper cleanup
"""

import hologram_ffi as hg
import json

def main():
    print("=" * 60)
    print("Hologram FFI - Simple Tensor Example")
    print("=" * 60)
    
    # Create executor and buffer
    print("\n🏗️ Setting up Executor and Buffer:")
    try:
        executor_handle = hg.new_executor()
        print(f"✅ Created executor: {executor_handle}")
        
        buffer_handle = hg.executor_allocate_buffer(executor_handle, 24)  # 2x3x4 tensor
        print(f"✅ Created buffer: {buffer_handle}")
        
    except Exception as e:
        print(f"❌ Setup failed: {e}")
        return
    
    # Create tensor
    print("\n📦 Tensor Creation:")
    try:
        shape = [2, 3, 4]
        tensor_handle = hg.tensor_from_buffer(buffer_handle, json.dumps(shape))
        print(f"✅ Created tensor with shape {shape}: {tensor_handle}")
        
    except Exception as e:
        print(f"❌ Tensor creation failed: {e}")
        hg.executor_cleanup(executor_handle)
        return
    
    # Tensor introspection
    print("\n🔍 Tensor Introspection:")
    try:
        # Get tensor properties
        tensor_shape = hg.tensor_shape(tensor_handle)
        tensor_ndim = hg.tensor_ndim(tensor_handle)
        tensor_numel = hg.tensor_numel(tensor_handle)
        tensor_is_contiguous = hg.tensor_is_contiguous(tensor_handle)
        
        print(f"Tensor Properties:")
        print(f"  Shape: {json.loads(tensor_shape)}")
        print(f"  Dimensions: {tensor_ndim}")
        print(f"  Number of elements: {tensor_numel}")
        print(f"  Is contiguous: {tensor_is_contiguous}")
        
    except Exception as e:
        print(f"❌ Tensor introspection failed: {e}")
    
    # Simple tensor operations
    print("\n⚙️ Simple Tensor Operations:")
    try:
        # Test reshape (simple case)
        new_shape = [6, 4]
        reshaped_tensor = hg.tensor_reshape(tensor_handle, json.dumps(new_shape))
        reshaped_shape = hg.tensor_shape(reshaped_tensor)
        print(f"✅ Reshaped tensor to {new_shape}: {json.loads(reshaped_shape)}")
        
        # Cleanup reshaped tensor
        hg.tensor_cleanup(reshaped_tensor)
        
    except Exception as e:
        print(f"❌ Tensor operations failed: {e}")
    
    # Test Atlas state (independent of executor)
    print("\n🌐 Atlas State Management:")
    try:
        phase = hg.atlas_phase()
        print(f"✅ Atlas phase: {phase}")
        
        resonance = hg.atlas_resonance_at(0)
        print(f"✅ Atlas resonance at class 0: {resonance}")
        
    except Exception as e:
        print(f"❌ Atlas state management failed: {e}")
    
    # Cleanup
    print("\n🧹 Cleanup:")
    try:
        hg.tensor_cleanup(tensor_handle)
        hg.executor_cleanup(executor_handle)
        print("✅ All resources cleaned up successfully")
    except Exception as e:
        print(f"❌ Cleanup failed: {e}")
    
    print("\n✅ Simple tensor example completed!")

if __name__ == "__main__":
    main()
