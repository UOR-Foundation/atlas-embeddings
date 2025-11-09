#!/usr/bin/env python3
"""
Basic Hologram FFI Usage Example

This example demonstrates how to use hologram-ffi for basic operations
that could be integrated into PyTorch models.
"""

import hologram_ffi as hg
import sys
import os
import json

# Add hologram-ffi to path if not already available
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..',
                'crates', 'hologram-ffi', 'interfaces', 'python'))


def vector_operations_example():
    """
    Demonstrate basic vector operations using hologram-ffi
    """
    print("\n" + "="*60)
    print("Vector Operations Example")
    print("="*60)

    # Create executor
    executor = hg.new_executor()
    print(f"✓ Executor created: {executor}")

    # Allocate buffers for vector addition
    size = 1000
    buffer_a = hg.executor_allocate_buffer(executor, size)
    buffer_b = hg.executor_allocate_buffer(executor, size)
    buffer_c = hg.executor_allocate_buffer(executor, size)
    print(f"✓ Buffers allocated")

    # Fill buffers with test data
    data_a = [1.5] * size
    data_b = [2.3] * size

    hg.buffer_copy_from_slice(executor, buffer_a, json.dumps(data_a))
    hg.buffer_copy_from_slice(executor, buffer_b, json.dumps(data_b))
    print(f"✓ Buffers filled with data")

    # Perform vector operations via hologram
    print("\nPerforming vector operations...")

    # Addition
    hg.vector_add_f32(executor, buffer_a, buffer_b, buffer_c, size)
    result_json = hg.buffer_to_vec(executor, buffer_c)
    result = json.loads(result_json)
    print(f"  Addition: a[0] + b[0] = {data_a[0]} + {data_b[0]} = {result[0]}")

    # Multiplication
    hg.vector_mul_f32(executor, buffer_a, buffer_b, buffer_c, size)
    result_json = hg.buffer_to_vec(executor, buffer_c)
    result = json.loads(result_json)
    print(
        f"  Multiplication: a[0] * b[0] = {data_a[0]} * {data_b[0]} = {result[0]}")

    # Subtraction
    hg.vector_sub_f32(executor, buffer_a, buffer_b, buffer_c, size)
    result_json = hg.buffer_to_vec(executor, buffer_c)
    result = json.loads(result_json)
    print(
        f"  Subtraction: a[0] - b[0] = {data_a[0]} - {data_b[0]} = {result[0]}")

    # Division
    hg.vector_div_f32(executor, buffer_a, buffer_b, buffer_c, size)
    result_json = hg.buffer_to_vec(executor, buffer_c)
    result = json.loads(result_json)
    print(
        f"  Division: a[0] / b[0] = {data_a[0]} / {data_b[0]} = {result[0]:.4f}")

    # Cleanup
    hg.buffer_cleanup(buffer_a)
    hg.buffer_cleanup(buffer_b)
    hg.buffer_cleanup(buffer_c)
    hg.executor_cleanup(executor)

    print("✓ Cleanup successful")


def reduction_example():
    """
    Demonstrate reduction operations (sum, min, max)
    """
    print("\n" + "="*60)
    print("Reduction Operations Example")
    print("="*60)

    executor = hg.new_executor()

    # Create test data
    size = 100
    # [1.0, 2.0, 3.0, ..., 100.0]
    data = [float(x) for x in range(1, size + 1)]

    buffer_input = hg.executor_allocate_buffer(executor, size)
    buffer_output = hg.executor_allocate_buffer(
        executor, 10)  # Need space for reductions
    hg.buffer_copy_from_slice(executor, buffer_input, json.dumps(data))

    # Sum reduction
    result = hg.reduce_sum_f32(executor, buffer_input, buffer_output, size)
    expected_sum = sum(data)
    print(f"✓ Sum reduction: {result} (expected: {expected_sum})")

    # Min reduction
    result = hg.reduce_min_f32(executor, buffer_input, buffer_output, size)
    expected_min = min(data)
    print(f"✓ Min reduction: {result} (expected: {expected_min})")

    # Max reduction
    result = hg.reduce_max_f32(executor, buffer_input, buffer_output, size)
    expected_max = max(data)
    print(f"✓ Max reduction: {result} (expected: {expected_max})")

    # Cleanup
    hg.buffer_cleanup(buffer_input)
    hg.buffer_cleanup(buffer_output)
    hg.executor_cleanup(executor)


def activation_example():
    """
    Demonstrate activation functions (sigmoid, tanh, gelu, relu)
    """
    print("\n" + "="*60)
    print("Activation Functions Example")
    print("="*60)

    executor = hg.new_executor()

    # Create test data
    size = 10
    # Test with values ranging from -2 to 2
    data = [-2.0, -1.0, -0.0, 1.0, 2.0, -1.5, 0.5, 1.5, -0.5, 0.0]

    buffer_input = hg.executor_allocate_buffer(executor, size)
    buffer_output = hg.executor_allocate_buffer(executor, size)
    hg.buffer_copy_from_slice(executor, buffer_input, json.dumps(data))

    # Test ReLU: max(0, x)
    hg.vector_relu_f32(executor, buffer_input, buffer_output, size)
    result_json = hg.buffer_to_vec(executor, buffer_output)
    result = json.loads(result_json)
    print(f"✓ ReLU activation:")
    print(f"  Input:  {[f'{x:5.2f}' for x in data[:5]]}")
    print(f"  Output: {[f'{x:5.2f}' for x in result[:5]]}")

    # Cleanup
    hg.buffer_cleanup(buffer_input)
    hg.buffer_cleanup(buffer_output)
    hg.executor_cleanup(executor)


def pytorch_integration_pattern():
    """
    Show how this could be integrated with PyTorch
    """
    print("\n" + "="*60)
    print("PyTorch Integration Pattern")
    print("="*60)

    print("""
To integrate hologram-ffi with PyTorch:

1. For Linear Layers (GEMM):
   - Convert PyTorch weight tensors to hologram buffers
   - Use hg.gemm_f32() for matrix multiplication
   - Convert results back to PyTorch tensors

2. For Activations:
   - Use hg.vector_relu_f32(), hg.sigmoid_f32(), etc.
   - These can be used in PyTorch custom Function classes

3. For Loss Functions:
   - Use hg.mse_loss_f32(), hg.cross_entropy_loss_f32(), etc.
   - Integrate into PyTorch loss computation

4. For Reductions:
   - Use hg.reduce_sum_f32(), etc. for gradient accumulation
   - Useful for distributed training

Example pattern for a custom layer:

    class HologramLinear(torch.nn.Module):
        def __init__(self, in_features, out_features):
            super().__init__()
            self.executor = hg.new_executor()
            self.weight_buf = allocate_weight_buffer()
            # ...
        
        def forward(self, x):
            # Convert PyTorch tensor to hologram buffer
            x_buf = tensor_to_buffer(x, self.executor)
            
            # Execute GEMM
            hg.gemm_f32(m, n, k)  # Matrix dimensions
            
            # Convert back to PyTorch tensor
            return buffer_to_tensor(result_buf)
    
    ✓ Integration pattern demonstrated
    """)


def main():
    """
    Main entry point
    """
    print("\n" + "="*60)
    print("Hologram FFI Usage Examples")
    print("="*60)

    print(f"Hologram FFI Version: {hg.get_version()}")

    # Run examples
    vector_operations_example()
    reduction_example()
    activation_example()
    pytorch_integration_pattern()

    print("\n" + "="*60)
    print("Examples Complete")
    print("="*60)


if __name__ == "__main__":
    main()
