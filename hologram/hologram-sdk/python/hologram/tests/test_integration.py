"""
Integration tests for hologram Python bindings.

Tests complete workflows end-to-end.

Note: Requires hologram_ffi to be built and available.
"""

import pytest
import numpy as np

pytest.importorskip("hologram_ffi", reason="hologram_ffi not available")

import hologram as hg


class TestIntegrationWorkflows:
    """Test complete workflows end-to-end."""

    def test_complete_vector_operation_workflow(self):
        """Test complete workflow: allocate, transfer, compute, read."""
        with hg.Executor(backend='cpu') as exec:
            # Allocate buffers
            buf_a = exec.allocate(1000)
            buf_b = exec.allocate(1000)
            buf_c = exec.allocate(1000)

            # Create test data
            data_a = np.arange(1000, dtype=np.float32)
            data_b = np.ones(1000, dtype=np.float32) * 2.0

            # Transfer to buffers
            buf_a.from_numpy(data_a)
            buf_b.from_numpy(data_b)

            # Execute multiple operations
            hg.ops.vector_add(exec, buf_a, buf_b, buf_c)  # c = a + b
            hg.ops.vector_relu(exec, buf_c, buf_a)  # a = relu(c)
            hg.ops.scalar_mul(exec, buf_a, buf_b, 0.5)  # b = a * 0.5

            # Read results
            result = buf_b.to_numpy()

            # Verify correctness
            expected = np.maximum(0, data_a + data_b) * 0.5
            np.testing.assert_allclose(result, expected, rtol=1e-5)

    def test_chained_operations(self):
        """Test multiple chained operations."""
        with hg.Executor() as exec:
            buf_input = exec.allocate(500)
            buf_temp1 = exec.allocate(500)
            buf_temp2 = exec.allocate(500)
            buf_output = exec.allocate(500)

            # Create input
            data = np.linspace(-10, 10, 500, dtype=np.float32)
            buf_input.from_numpy(data)

            # Chain: abs -> add scalar -> mul -> relu
            hg.ops.vector_abs(exec, buf_input, buf_temp1)
            hg.ops.scalar_add(exec, buf_temp1, buf_temp2, 1.0)
            hg.ops.scalar_mul(exec, buf_temp2, buf_temp1, 2.0)
            hg.ops.vector_relu(exec, buf_temp1, buf_output)

            # Verify
            result = buf_output.to_numpy()
            expected = np.maximum(0, (np.abs(data) + 1.0) * 2.0)
            np.testing.assert_allclose(result, expected, rtol=1e-5)

    def test_reduction_workflow(self):
        """Test reduction operations workflow."""
        with hg.Executor() as exec:
            buf_input = exec.allocate(1000)
            buf_output = exec.allocate(3)  # Need 3 for temporaries

            # Create test data
            data = np.arange(1000, dtype=np.float32)
            buf_input.from_numpy(data)

            # Test sum
            sum_result = hg.ops.reduce_sum(exec, buf_input, buf_output)
            expected_sum = np.sum(data)
            np.testing.assert_allclose(sum_result, expected_sum, rtol=1e-4)

            # Test min
            min_result = hg.ops.reduce_min(exec, buf_input, buf_output)
            expected_min = np.min(data)
            assert abs(min_result - expected_min) < 1e-5

            # Test max
            max_result = hg.ops.reduce_max(exec, buf_input, buf_output)
            expected_max = np.max(data)
            assert abs(max_result - expected_max) < 1e-5

    def test_matrix_multiplication_workflow(self):
        """Test matrix multiplication workflow."""
        with hg.Executor() as exec:
            m, n, k = 16, 12, 8

            # Allocate buffers
            buf_a = exec.allocate(m * k)
            buf_b = exec.allocate(k * n)
            buf_c = exec.allocate(m * n)

            # Create matrices
            mat_a = np.random.randn(m, k).astype(np.float32)
            mat_b = np.random.randn(k, n).astype(np.float32)

            # Transfer
            buf_a.from_numpy(mat_a.flatten())
            buf_b.from_numpy(mat_b.flatten())

            # GEMM
            hg.ops.gemm(exec, buf_a, buf_b, buf_c, m, n, k)

            # Read result
            result = buf_c.to_numpy().reshape(m, n)

            # Verify
            expected = mat_a @ mat_b
            np.testing.assert_allclose(result, expected, rtol=1e-4)

    def test_activation_functions_workflow(self):
        """Test all activation functions in sequence."""
        with hg.Executor() as exec:
            size = 100
            buf_input = exec.allocate(size)
            buf_output = exec.allocate(size)

            # Test data
            data = np.linspace(-5, 5, size, dtype=np.float32)

            # Test sigmoid
            buf_input.from_numpy(data)
            hg.ops.sigmoid(exec, buf_input, buf_output)
            result_sigmoid = buf_output.to_numpy()
            expected_sigmoid = 1.0 / (1.0 + np.exp(-data))
            np.testing.assert_allclose(result_sigmoid, expected_sigmoid, rtol=1e-5)

            # Test tanh
            buf_input.from_numpy(data)
            hg.ops.tanh(exec, buf_input, buf_output)
            result_tanh = buf_output.to_numpy()
            expected_tanh = np.tanh(data)
            np.testing.assert_allclose(result_tanh, expected_tanh, rtol=1e-5)

            # Test relu
            buf_input.from_numpy(data)
            hg.ops.vector_relu(exec, buf_input, buf_output)
            result_relu = buf_output.to_numpy()
            expected_relu = np.maximum(0, data)
            np.testing.assert_allclose(result_relu, expected_relu, rtol=1e-5)

    def test_buffer_copy_and_fill(self):
        """Test buffer copy and fill operations."""
        with hg.Executor() as exec:
            buf_a = exec.allocate(100)
            buf_b = exec.allocate(100)

            # Fill buf_a
            buf_a.fill(42.0)
            result_a = buf_a.to_numpy()
            assert np.all(result_a == 42.0)

            # Copy to buf_b
            buf_b.copy_from(buf_a)
            result_b = buf_b.to_numpy()
            assert np.all(result_b == 42.0)

            # Modify buf_b
            buf_b.fill(99.0)
            result_b_new = buf_b.to_numpy()
            assert np.all(result_b_new == 99.0)

            # buf_a should be unchanged
            result_a_check = buf_a.to_numpy()
            assert np.all(result_a_check == 42.0)

    def test_zero_copy_roundtrip_performance(self):
        """Test zero-copy roundtrip maintains data integrity."""
        with hg.Executor() as exec:
            for size in [100, 1000, 10000]:
                buf = exec.allocate(size)

                # Original data
                original = np.random.randn(size).astype(np.float32)

                # Write and read back
                buf.from_numpy(original)
                result = buf.to_numpy()

                # Should be exactly equal (bit-for-bit)
                np.testing.assert_array_equal(result, original)

    def test_large_scale_operation(self):
        """Test large-scale operation (100K elements)."""
        size = 100000

        with hg.Executor() as exec:
            buf_a = exec.allocate(size)
            buf_b = exec.allocate(size)
            buf_c = exec.allocate(size)

            # Large arrays
            data_a = np.random.randn(size).astype(np.float32)
            data_b = np.random.randn(size).astype(np.float32)

            buf_a.from_numpy(data_a)
            buf_b.from_numpy(data_b)

            # Execute operation
            hg.ops.vector_add(exec, buf_a, buf_b, buf_c)

            # Verify correctness
            result = buf_c.to_numpy()
            expected = data_a + data_b

            np.testing.assert_allclose(result, expected, rtol=1e-5)


class TestErrorHandling:
    """Test error handling and edge cases."""

    def test_size_mismatch_error(self):
        """Test error when array size doesn't match buffer size."""
        with hg.Executor() as exec:
            buf = exec.allocate(100)

            wrong_size_data = np.zeros(50, dtype=np.float32)

            with pytest.raises(ValueError, match="doesn't match"):
                buf.from_numpy(wrong_size_data)

    def test_wrong_dtype_error(self):
        """Test error when array dtype is wrong."""
        with hg.Executor() as exec:
            buf = exec.allocate(100)

            wrong_dtype_data = np.zeros(100, dtype=np.float64)  # float64 instead of float32

            with pytest.raises(ValueError, match="dtype"):
                buf.from_numpy(wrong_dtype_data)

    def test_freed_buffer_error(self):
        """Test error when using freed buffer."""
        with hg.Executor() as exec:
            buf = exec.allocate(100)
            buf.free()

            with pytest.raises(RuntimeError, match="freed"):
                buf.to_numpy()

    def test_invalid_backend(self):
        """Test error with invalid backend."""
        with pytest.raises(ValueError, match="Invalid backend"):
            hg.Executor(backend='invalid_backend')

    def test_reduction_buffer_size_error(self):
        """Test error when reduction output buffer is too small."""
        with hg.Executor() as exec:
            buf_input = exec.allocate(100)
            buf_output = exec.allocate(1)  # Too small! Need 3

            data = np.ones(100, dtype=np.float32)
            buf_input.from_numpy(data)

            with pytest.raises(ValueError, match="at least 3 elements"):
                hg.ops.reduce_sum(exec, buf_input, buf_output)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
