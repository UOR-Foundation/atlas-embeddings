"""
Basic tests for hologram Python bindings.

Note: These tests require hologram_ffi to be built and available.
Run 'cargo build-ffi' in the hologram repository first.
"""

import pytest
import numpy as np


# Skip all tests if hologram_ffi is not available
pytest.importorskip("hologram_ffi", reason="hologram_ffi not available")

import hologram as hg


class TestBackend:
    """Test backend utilities."""

    def test_backend_type_enum(self):
        """Test BackendType enum."""
        assert hg.BackendType.CPU.value == "cpu"
        assert hg.BackendType.METAL.value == "metal"
        assert hg.BackendType.CUDA.value == "cuda"
        assert hg.BackendType.AUTO.value == "auto"

    def test_is_metal_available(self):
        """Test Metal availability check."""
        result = hg.is_metal_available()
        assert isinstance(result, bool)

    def test_is_cuda_available(self):
        """Test CUDA availability check."""
        result = hg.is_cuda_available()
        assert isinstance(result, bool)

    def test_get_default_backend(self):
        """Test default backend selection."""
        backend = hg.get_default_backend()
        assert backend in {"cpu", "metal", "cuda"}


class TestExecutor:
    """Test Executor class."""

    def test_create_cpu_executor(self):
        """Test creating CPU executor."""
        exec = hg.Executor(backend='cpu')
        assert exec.handle > 0
        assert exec.backend == 'cpu'
        exec.cleanup()

    def test_executor_context_manager(self):
        """Test executor as context manager."""
        with hg.Executor(backend='cpu') as exec:
            assert exec.handle > 0
            assert not exec._freed
        # Should be freed after context exit
        assert exec._freed

    def test_allocate_buffer(self):
        """Test buffer allocation."""
        with hg.Executor(backend='cpu') as exec:
            buf = exec.allocate(1024)
            assert buf.size == 1024
            assert buf.dtype == np.float32
            assert not buf._freed

    def test_invalid_backend(self):
        """Test invalid backend raises error."""
        with pytest.raises(ValueError, match="Invalid backend"):
            hg.Executor(backend='invalid')


class TestBuffer:
    """Test Buffer class."""

    def test_buffer_properties(self):
        """Test buffer properties."""
        with hg.Executor(backend='cpu') as exec:
            buf = exec.allocate(100)
            assert buf.size == 100
            assert len(buf) == 100
            assert buf.dtype == np.float32
            assert buf.nbytes == 100 * 4  # 4 bytes per float32

    def test_from_numpy(self):
        """Test zero-copy from NumPy."""
        with hg.Executor(backend='cpu') as exec:
            buf = exec.allocate(10)
            data = np.arange(10, dtype=np.float32)
            buf.from_numpy(data)  # Should not raise

    def test_to_numpy(self):
        """Test zero-copy to NumPy."""
        with hg.Executor(backend='cpu') as exec:
            buf = exec.allocate(10)
            result = buf.to_numpy()
            assert isinstance(result, np.ndarray)
            assert result.shape == (10,)
            assert result.dtype == np.float32

    def test_fill(self):
        """Test buffer fill operation."""
        with hg.Executor(backend='cpu') as exec:
            buf = exec.allocate(100)
            buf.fill(42.0)
            result = buf.to_numpy()
            np.testing.assert_array_equal(result, np.full(100, 42.0, dtype=np.float32))

    def test_copy_from(self):
        """Test buffer copy operation."""
        with hg.Executor(backend='cpu') as exec:
            buf_a = exec.allocate(10)
            buf_b = exec.allocate(10)

            buf_a.fill(123.0)
            buf_b.copy_from(buf_a)

            result = buf_b.to_numpy()
            np.testing.assert_array_equal(result, np.full(10, 123.0, dtype=np.float32))

    def test_roundtrip(self):
        """Test roundtrip: NumPy → Buffer → NumPy."""
        with hg.Executor(backend='cpu') as exec:
            buf = exec.allocate(100)

            # Original data
            original = np.arange(100, dtype=np.float32)

            # Write to buffer
            buf.from_numpy(original)

            # Read back
            result = buf.to_numpy()

            # Should match
            np.testing.assert_array_equal(result, original)


class TestOperations:
    """Test operation wrappers."""

    def test_vector_add(self):
        """Test vector addition."""
        with hg.Executor(backend='cpu') as exec:
            buf_a = exec.allocate(100)
            buf_b = exec.allocate(100)
            buf_c = exec.allocate(100)

            data_a = np.ones(100, dtype=np.float32)
            data_b = np.ones(100, dtype=np.float32) * 2.0

            buf_a.from_numpy(data_a)
            buf_b.from_numpy(data_b)

            hg.ops.vector_add(exec, buf_a, buf_b, buf_c)

            result = buf_c.to_numpy()
            expected = data_a + data_b

            np.testing.assert_allclose(result, expected, rtol=1e-5)

    def test_vector_mul(self):
        """Test vector multiplication."""
        with hg.Executor(backend='cpu') as exec:
            buf_a = exec.allocate(50)
            buf_b = exec.allocate(50)
            buf_c = exec.allocate(50)

            data_a = np.arange(50, dtype=np.float32)
            data_b = np.arange(50, dtype=np.float32) * 2.0

            buf_a.from_numpy(data_a)
            buf_b.from_numpy(data_b)

            hg.ops.vector_mul(exec, buf_a, buf_b, buf_c)

            result = buf_c.to_numpy()
            expected = data_a * data_b

            np.testing.assert_allclose(result, expected, rtol=1e-5)

    def test_vector_relu(self):
        """Test ReLU activation."""
        with hg.Executor(backend='cpu') as exec:
            buf_a = exec.allocate(10)
            buf_b = exec.allocate(10)

            # Mix of positive and negative values
            data = np.array([-2, -1, 0, 1, 2, -3, 4, -5, 6, -7], dtype=np.float32)

            buf_a.from_numpy(data)
            hg.ops.vector_relu(exec, buf_a, buf_b)

            result = buf_b.to_numpy()
            expected = np.maximum(0, data)

            np.testing.assert_array_equal(result, expected)

    def test_scalar_add(self):
        """Test scalar addition."""
        with hg.Executor(backend='cpu') as exec:
            buf_a = exec.allocate(10)
            buf_b = exec.allocate(10)

            data = np.arange(10, dtype=np.float32)
            buf_a.from_numpy(data)

            hg.ops.scalar_add(exec, buf_a, buf_b, 10.0)

            result = buf_b.to_numpy()
            expected = data + 10.0

            np.testing.assert_allclose(result, expected, rtol=1e-5)

    def test_reduce_sum(self):
        """Test sum reduction."""
        with hg.Executor(backend='cpu') as exec:
            buf_input = exec.allocate(100)
            buf_output = exec.allocate(3)  # Need 3 elements for temporaries

            data = np.arange(100, dtype=np.float32)
            buf_input.from_numpy(data)

            result = hg.ops.reduce_sum(exec, buf_input, buf_output)

            expected = np.sum(data)
            np.testing.assert_allclose(result, expected, rtol=1e-4)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
