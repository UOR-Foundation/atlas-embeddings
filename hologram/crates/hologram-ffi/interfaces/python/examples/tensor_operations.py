#!/usr/bin/env python3
"""
Tensor Operations Example

This example demonstrates comprehensive tensor operations including:
- Tensor creation from buffers
- Tensor introspection (shape, strides, properties)
- Tensor operations (reshape, transpose, permute, view)
- Tensor slicing (select, narrow, slice)
- Matrix multiplication
- Broadcasting operations
- Proper cleanup
"""

import hologram_ffi as hg
import json

def main():
    print("=" * 60)
    print("Hologram FFI - Tensor Operations Example")
    print("=" * 60)
    
    # Create executor and buffers
    print("\n🏗️ Setting up Executor and Buffers:")
    try:
        executor_handle = hg.new_executor()
        print(f"✅ Created executor: {executor_handle}")
        
        # Create buffer for tensor
        buffer_handle = hg.executor_allocate_buffer(executor_handle, 24)  # 2x3x4 tensor
        print(f"✅ Created buffer: {buffer_handle}")
        
    except Exception as e:
        print(f"❌ Setup failed: {e}")
        return
    
    # Tensor creation
    print("\n📦 Tensor Creation:")
    try:
        # Create tensor from buffer with shape [2, 3, 4]
        shape = [2, 3, 4]
        tensor_handle = hg.tensor_from_buffer(buffer_handle, json.dumps(shape))
        print(f"✅ Created tensor with shape {shape}: {tensor_handle}")
        
        # Create tensor with custom strides
        strides = [12, 4, 1]  # Row-major strides
        buffer_handle2 = hg.executor_allocate_buffer(executor_handle, 24)
        tensor_handle2 = hg.tensor_from_buffer_with_strides(buffer_handle2, json.dumps(shape), json.dumps(strides))
        print(f"✅ Created tensor with custom strides {strides}: {tensor_handle2}")
        
    except Exception as e:
        print(f"❌ Tensor creation failed: {e}")
        return
    
    # Tensor introspection
    print("\n🔍 Tensor Introspection:")
    try:
        # Get tensor properties
        tensor_shape = hg.tensor_shape(tensor_handle)
        tensor_strides = hg.tensor_strides(tensor_handle)
        tensor_offset = hg.tensor_offset(tensor_handle)
        tensor_ndim = hg.tensor_ndim(tensor_handle)
        tensor_numel = hg.tensor_numel(tensor_handle)
        tensor_is_contiguous = hg.tensor_is_contiguous(tensor_handle)
        
        print(f"Tensor Properties:")
        print(f"  Shape: {json.loads(tensor_shape)}")
        print(f"  Strides: {json.loads(tensor_strides)}")
        print(f"  Offset: {tensor_offset}")
        print(f"  Dimensions: {tensor_ndim}")
        print(f"  Number of elements: {tensor_numel}")
        print(f"  Is contiguous: {tensor_is_contiguous}")
        
        # Get underlying buffer
        tensor_buffer_handle = hg.tensor_buffer(tensor_handle)
        print(f"  Underlying buffer: {tensor_buffer_handle}")
        
    except Exception as e:
        print(f"❌ Tensor introspection failed: {e}")
    
    # Tensor operations
    print("\n⚙️ Tensor Operations:")
    try:
        # Reshape tensor
        new_shape = [6, 4]
        reshaped_tensor = hg.tensor_reshape(tensor_handle, json.dumps(new_shape))
        reshaped_shape = hg.tensor_shape(reshaped_tensor)
        print(f"✅ Reshaped tensor to {new_shape}: {json.loads(reshaped_shape)}")
        
        # Cleanup reshaped tensor
        hg.tensor_cleanup(reshaped_tensor)
        
        # Create new tensor for transpose operation
        buffer_handle3 = hg.executor_allocate_buffer(executor_handle, 24)
        tensor_handle3 = hg.tensor_from_buffer(buffer_handle3, json.dumps([6, 4]))
        
        # Transpose tensor (for 2D tensors)
        transposed_tensor = hg.tensor_transpose(tensor_handle3)
        transposed_shape = hg.tensor_shape(transposed_tensor)
        print(f"✅ Transposed tensor: {json.loads(transposed_shape)}")
        
        # Cleanup transposed tensor
        hg.tensor_cleanup(transposed_tensor)
        
        # Create new tensor for permute operation
        buffer_handle4 = hg.executor_allocate_buffer(executor_handle, 24)
        tensor_handle4 = hg.tensor_from_buffer(buffer_handle4, json.dumps([4, 6]))
        
        # Permute dimensions
        perm_dims = [1, 0]  # Swap dimensions
        permuted_tensor = hg.tensor_permute(tensor_handle4, json.dumps(perm_dims))
        permuted_shape = hg.tensor_shape(permuted_tensor)
        print(f"✅ Permuted tensor with dims {perm_dims}: {json.loads(permuted_shape)}")
        
        # Cleanup permuted tensor
        hg.tensor_cleanup(permuted_tensor)
        
        # Create new tensor for view_1d operation
        buffer_handle5 = hg.executor_allocate_buffer(executor_handle, 24)
        tensor_handle5 = hg.tensor_from_buffer(buffer_handle5, json.dumps([6, 4]))
        
        # Create 1D view
        view_1d = hg.tensor_view_1d(tensor_handle5)
        view_shape = hg.tensor_shape(view_1d)
        print(f"✅ Created 1D view: {json.loads(view_shape)}")
        
        # Cleanup view_1d tensor
        hg.tensor_cleanup(view_1d)
        
    except Exception as e:
        print(f"❌ Tensor operations failed: {e}")
    
    # Tensor slicing operations
    print("\n✂️ Tensor Slicing Operations:")
    try:
        # Create a 3D tensor for slicing
        buffer_handle3 = hg.executor_allocate_buffer(executor_handle, 24)
        tensor_3d = hg.tensor_from_buffer(buffer_handle3, json.dumps([2, 3, 4]))
        
        # Select operation (reduces dimensionality)
        selected_tensor = hg.tensor_select(tensor_3d, 0, 1)  # Select index 1 along dim 0
        selected_shape = hg.tensor_shape(selected_tensor)
        print(f"✅ Selected tensor: {json.loads(selected_shape)}")
        
        # Narrow operation
        narrowed_tensor = hg.tensor_narrow(tensor_3d, 1, 1, 2)  # Narrow dim 1 from index 1, length 2
        narrowed_shape = hg.tensor_shape(narrowed_tensor)
        print(f"✅ Narrowed tensor: {json.loads(narrowed_shape)}")
        
        # Slice operation
        sliced_tensor = hg.tensor_slice(tensor_3d, 2, 1, 3, 1)  # Slice dim 2 from 1 to 3 with step 1
        sliced_shape = hg.tensor_shape(sliced_tensor)
        print(f"✅ Sliced tensor: {json.loads(sliced_shape)}")
        
        # Cleanup slicing tensors
        hg.tensor_cleanup(selected_tensor)
        hg.tensor_cleanup(narrowed_tensor)
        hg.tensor_cleanup(sliced_tensor)
        hg.tensor_cleanup(tensor_3d)
        
    except Exception as e:
        print(f"❌ Tensor slicing failed: {e}")
    
    # Matrix multiplication
    print("\n🔢 Matrix Multiplication:")
    try:
        # Create two 2D tensors for matrix multiplication
        buffer_a = hg.executor_allocate_buffer(executor_handle, 6)  # 2x3 matrix
        buffer_b = hg.executor_allocate_buffer(executor_handle, 8)  # 2x4 matrix
        
        tensor_a = hg.tensor_from_buffer(buffer_a, json.dumps([2, 3]))
        tensor_b = hg.tensor_from_buffer(buffer_b, json.dumps([2, 4]))
        
        # Matrix multiplication
        result_tensor = hg.tensor_matmul(executor_handle, tensor_a, tensor_b)
        result_shape = hg.tensor_shape(result_tensor)
        print(f"✅ Matrix multiplication result shape: {json.loads(result_shape)}")
        
        # Cleanup matrix multiplication tensors
        hg.tensor_cleanup(tensor_a)
        hg.tensor_cleanup(tensor_b)
        hg.tensor_cleanup(result_tensor)
        
    except Exception as e:
        print(f"❌ Matrix multiplication failed: {e}")
    
    # Broadcasting operations
    print("\n📡 Broadcasting Operations:")
    try:
        # Create tensors for broadcasting
        buffer_c = hg.executor_allocate_buffer(executor_handle, 4)  # 2x2 matrix
        buffer_d = hg.executor_allocate_buffer(executor_handle, 2)  # 2x1 vector
        
        tensor_c = hg.tensor_from_buffer(buffer_c, json.dumps([2, 2]))
        tensor_d = hg.tensor_from_buffer(buffer_d, json.dumps([2, 1]))
        
        # Check broadcast compatibility
        is_compatible = hg.tensor_is_broadcast_compatible(tensor_c, tensor_d)
        print(f"✅ Broadcast compatibility: {is_compatible}")
        
        # Get broadcast shape
        broadcast_shape = hg.tensor_broadcast_shape(tensor_c, tensor_d)
        print(f"✅ Broadcast shape: {json.loads(broadcast_shape)}")
        
        # Cleanup broadcasting tensors
        hg.tensor_cleanup(tensor_c)
        hg.tensor_cleanup(tensor_d)
        
    except Exception as e:
        print(f"❌ Broadcasting operations failed: {e}")
    
    # Cleanup
    print("\n🧹 Cleanup:")
    try:
        hg.tensor_cleanup(tensor_handle)
        hg.tensor_cleanup(tensor_handle2)
        hg.executor_cleanup(executor_handle)
        print("✅ All resources cleaned up successfully")
    except Exception as e:
        print(f"❌ Cleanup failed: {e}")
    
    print("\n✅ Tensor operations example completed!")

if __name__ == "__main__":
    main()
