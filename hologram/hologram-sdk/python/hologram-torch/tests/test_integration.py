"""
Integration tests for hologram-torch PyTorch integration.

Tests complete workflows end-to-end with PyTorch tensors.

Note: Requires hologram_ffi, hologram, and torch to be available.
"""

import pytest
import numpy as np

pytest.importorskip("hologram_ffi", reason="hologram_ffi not available")
pytest.importorskip("torch", reason="torch not available")

import torch
import hologram_torch as hg


class TestFunctionalAPIIntegration:
    """Test functional API end-to-end workflows."""

    def test_basic_tensor_operations(self):
        """Test basic tensor operations."""
        exec = hg.Executor(backend='cpu')

        a = torch.tensor([1.0, 2.0, 3.0, 4.0], dtype=torch.float32)
        b = torch.tensor([5.0, 6.0, 7.0, 8.0], dtype=torch.float32)

        # Addition
        c = hg.functional.add(exec, a, b)
        expected_c = a + b
        torch.testing.assert_close(c, expected_c)

        # Multiplication
        d = hg.functional.mul(exec, a, b)
        expected_d = a * b
        torch.testing.assert_close(d, expected_d)

        # Subtraction
        e = hg.functional.sub(exec, a, b)
        expected_e = a - b
        torch.testing.assert_close(e, expected_e)

    def test_activation_functions(self):
        """Test all activation functions."""
        exec = hg.Executor()

        x = torch.linspace(-5, 5, 100, dtype=torch.float32)

        # ReLU
        y_relu = hg.functional.relu(exec, x)
        expected_relu = torch.relu(x)
        torch.testing.assert_close(y_relu, expected_relu)

        # Sigmoid
        y_sigmoid = hg.functional.sigmoid(exec, x)
        expected_sigmoid = torch.sigmoid(x)
        torch.testing.assert_close(y_sigmoid, expected_sigmoid, rtol=1e-5, atol=1e-5)

        # Tanh
        y_tanh = hg.functional.tanh(exec, x)
        expected_tanh = torch.tanh(x)
        torch.testing.assert_close(y_tanh, expected_tanh, rtol=1e-5, atol=1e-5)

    def test_linear_transformation(self):
        """Test linear transformation."""
        exec = hg.Executor()

        batch_size, in_features, out_features = 8, 16, 12

        x = torch.randn(batch_size, in_features)
        weight = torch.randn(out_features, in_features)
        bias = torch.randn(out_features)

        # Hologram linear
        y_hologram = hg.functional.linear(exec, x, weight, bias)

        # PyTorch linear
        y_pytorch = torch.nn.functional.linear(x, weight, bias)

        # Should match
        torch.testing.assert_close(y_hologram, y_pytorch, rtol=1e-4, atol=1e-4)

    def test_loss_function(self):
        """Test MSE loss."""
        exec = hg.Executor()

        pred = torch.randn(100)
        target = torch.randn(100)

        # Hologram MSE
        loss_hologram = hg.functional.mse_loss(exec, pred, target)

        # PyTorch MSE
        loss_pytorch = torch.nn.functional.mse_loss(pred, target)

        # Should match
        assert abs(loss_hologram - loss_pytorch) < 1e-4

    def test_chained_operations(self):
        """Test chaining multiple operations."""
        exec = hg.Executor()

        x = torch.randn(100)
        y = torch.randn(100)

        # Chain: (x + y) * relu(x)
        sum_result = hg.functional.add(exec, x, y)
        relu_result = hg.functional.relu(exec, x)
        final_result = hg.functional.mul(exec, sum_result, relu_result)

        # Expected
        expected = (x + y) * torch.relu(x)

        torch.testing.assert_close(final_result, expected)


class TestModuleAPIIntegration:
    """Test nn.Module API end-to-end workflows."""

    def test_linear_module(self):
        """Test Linear module."""
        linear = hg.nn.Linear(10, 5)
        x = torch.randn(32, 10)

        y = linear(x)

        assert y.shape == (32, 5)
        assert y.dtype == torch.float32

    def test_activation_modules(self):
        """Test activation modules."""
        x = torch.randn(100)

        # ReLU
        relu = hg.nn.ReLU()
        y_relu = relu(x)
        expected_relu = torch.relu(x)
        torch.testing.assert_close(y_relu, expected_relu)

        # Sigmoid
        sigmoid = hg.nn.Sigmoid()
        y_sigmoid = sigmoid(x)
        expected_sigmoid = torch.sigmoid(x)
        torch.testing.assert_close(y_sigmoid, expected_sigmoid, rtol=1e-5, atol=1e-5)

        # Tanh
        tanh = hg.nn.Tanh()
        y_tanh = tanh(x)
        expected_tanh = torch.tanh(x)
        torch.testing.assert_close(y_tanh, expected_tanh, rtol=1e-5, atol=1e-5)

    def test_simple_network(self):
        """Test simple feedforward network."""
        class SimpleNet(torch.nn.Module):
            def __init__(self):
                super().__init__()
                self.fc1 = hg.nn.Linear(20, 10)
                self.relu = hg.nn.ReLU()
                self.fc2 = hg.nn.Linear(10, 5)

            def forward(self, x):
                x = self.fc1(x)
                x = self.relu(x)
                x = self.fc2(x)
                return x

        model = SimpleNet()
        x = torch.randn(16, 20)
        y = model(x)

        assert y.shape == (16, 5)
        assert y.dtype == torch.float32

    def test_mixed_pytorch_hologram_network(self):
        """Test mixing PyTorch and hologram layers."""
        model = torch.nn.Sequential(
            torch.nn.Linear(20, 15),       # PyTorch
            hg.nn.ReLU(),                  # Hologram
            torch.nn.Dropout(0.1),         # PyTorch
            hg.nn.Linear(15, 10),          # Hologram
            torch.nn.BatchNorm1d(10),      # PyTorch
            hg.nn.Tanh(),                  # Hologram
            torch.nn.Linear(10, 5)         # PyTorch
        )

        x = torch.randn(32, 20)
        y = model(x)

        assert y.shape == (32, 5)


class TestTrainingIntegration:
    """Test training workflows."""

    def test_forward_backward_pass(self):
        """Test forward and backward pass."""
        model = hg.nn.Linear(10, 5)
        criterion = hg.nn.MSELoss()
        optimizer = torch.optim.SGD(model.parameters(), lr=0.01)

        # Forward pass
        x = torch.randn(8, 10)
        target = torch.randn(8, 5)

        output = model(x)
        loss = criterion(output, target)

        # Backward pass
        optimizer.zero_grad()
        loss.backward()
        optimizer.step()

        # Should complete without error
        assert True

    def test_training_loop(self):
        """Test complete training loop."""
        model = torch.nn.Sequential(
            hg.nn.Linear(20, 10),
            hg.nn.ReLU(),
            hg.nn.Linear(10, 5)
        )

        criterion = hg.nn.MSELoss()
        optimizer = torch.optim.Adam(model.parameters(), lr=0.001)

        # Train for a few iterations
        for epoch in range(5):
            # Generate batch
            x = torch.randn(32, 20)
            target = torch.randn(32, 5)

            # Forward
            output = model(x)
            loss = criterion(output, target)

            # Backward
            optimizer.zero_grad()
            loss.backward()
            optimizer.step()

        # Should complete
        assert True

    def test_gradients_flow(self):
        """Test that gradients flow correctly."""
        linear = hg.nn.Linear(5, 3)
        relu = hg.nn.ReLU()

        x = torch.randn(2, 5, requires_grad=True)

        # Forward
        h = linear(x)
        y = relu(h)
        loss = y.sum()

        # Backward
        loss.backward()

        # Check gradients exist
        assert x.grad is not None
        assert linear.weight.grad is not None
        if linear.bias is not None:
            assert linear.bias.grad is not None


class TestTensorConversionUtils:
    """Test tensor conversion utilities."""

    def test_tensor_to_buffer_roundtrip(self):
        """Test tensor → buffer → tensor roundtrip."""
        exec = hg.Executor()

        original = torch.randn(100)
        buffer, _ = hg.utils.tensor_to_buffer(exec, original)
        result = hg.utils.buffer_to_tensor(buffer, original.shape)

        torch.testing.assert_close(result, original)

    def test_validate_tensor_compatible(self):
        """Test tensor compatibility validation."""
        # Valid tensor
        valid = torch.randn(100, dtype=torch.float32)
        hg.utils.validate_tensor_compatible(valid)  # Should not raise

        # Invalid dtype
        invalid_dtype = torch.randn(100, dtype=torch.float64)
        with pytest.raises(ValueError, match="float32"):
            hg.utils.validate_tensor_compatible(invalid_dtype)

    def test_multidimensional_tensors(self):
        """Test conversion of multi-dimensional tensors."""
        exec = hg.Executor()

        shapes = [(10, 20), (5, 10, 2), (2, 3, 4, 5)]

        for shape in shapes:
            original = torch.randn(*shape)
            buffer, _ = hg.utils.tensor_to_buffer(exec, original)
            result = hg.utils.buffer_to_tensor(buffer, shape)

            torch.testing.assert_close(result, original)


class TestLargeScale:
    """Test large-scale operations."""

    def test_large_tensor_operation(self):
        """Test operation on large tensors (100K elements)."""
        exec = hg.Executor()

        a = torch.randn(100000)
        b = torch.randn(100000)

        c = hg.functional.add(exec, a, b)
        expected = a + b

        torch.testing.assert_close(c, expected)

    def test_large_network_forward(self):
        """Test forward pass on large network."""
        model = torch.nn.Sequential(
            hg.nn.Linear(1000, 500),
            hg.nn.ReLU(),
            hg.nn.Linear(500, 250),
            hg.nn.ReLU(),
            hg.nn.Linear(250, 10)
        )

        x = torch.randn(64, 1000)  # Large batch
        y = model(x)

        assert y.shape == (64, 10)


class TestErrorHandling:
    """Test error handling."""

    def test_shape_mismatch_error(self):
        """Test error on shape mismatch."""
        exec = hg.Executor()

        a = torch.randn(10)
        b = torch.randn(20)  # Different size

        with pytest.raises(ValueError, match="shape"):
            hg.functional.add(exec, a, b)

    def test_non_cpu_tensor_error(self):
        """Test error with non-CPU tensor."""
        exec = hg.Executor()

        # This will only raise if CUDA is available
        if torch.cuda.is_available():
            a = torch.randn(10).cuda()
            b = torch.randn(10).cuda()

            with pytest.raises(ValueError, match="CPU"):
                hg.functional.add(exec, a, b)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
