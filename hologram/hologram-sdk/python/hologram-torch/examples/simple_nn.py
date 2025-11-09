#!/usr/bin/env python3
"""
Simple neural network example using hologram-torch.

Demonstrates:
- Building a model with hologram layers
- Forward pass
- Training loop with backpropagation
- Mixed PyTorch + hologram layers
"""

import torch
import torch.optim as optim
import hologram_torch as hg
import time


class SimpleNN(torch.nn.Module):
    """Simple feedforward network using hologram layers."""

    def __init__(self, input_size=128, hidden_size=64, output_size=10):
        super().__init__()
        self.fc1 = hg.nn.Linear(input_size, hidden_size)
        self.relu1 = hg.nn.ReLU()
        self.fc2 = hg.nn.Linear(hidden_size, hidden_size // 2)
        self.relu2 = hg.nn.ReLU()
        self.fc3 = hg.nn.Linear(hidden_size // 2, output_size)

    def forward(self, x):
        x = self.fc1(x)
        x = self.relu1(x)
        x = self.fc2(x)
        x = self.relu2(x)
        x = self.fc3(x)
        return x


def main():
    print("=" * 60)
    print("Hologram PyTorch Integration - Simple NN Example")
    print("=" * 60)
    print()

    # Set random seed for reproducibility
    torch.manual_seed(42)

    # Model parameters
    batch_size = 32
    input_size = 128
    hidden_size = 64
    output_size = 10
    num_epochs = 10
    learning_rate = 0.001

    print("Model Configuration:")
    print(f"  Input size: {input_size}")
    print(f"  Hidden size: {hidden_size}")
    print(f"  Output size: {output_size}")
    print(f"  Batch size: {batch_size}")
    print(f"  Learning rate: {learning_rate}")
    print()

    # Create model
    print("Creating model with hologram layers...")
    model = SimpleNN(input_size, hidden_size, output_size)
    print(model)
    print()

    # Loss and optimizer
    criterion = hg.nn.MSELoss()
    optimizer = optim.Adam(model.parameters(), lr=learning_rate)

    print("Starting training...")
    print()

    # Training loop
    for epoch in range(num_epochs):
        # Generate random training data
        inputs = torch.randn(batch_size, input_size)
        targets = torch.randn(batch_size, output_size)

        # Measure forward pass time
        start_time = time.perf_counter()

        # Forward pass
        outputs = model(inputs)
        loss = criterion(outputs, targets)

        # Backward pass
        optimizer.zero_grad()
        loss.backward()
        optimizer.step()

        forward_time = time.perf_counter() - start_time

        # Print progress
        print(f"Epoch [{epoch+1}/{num_epochs}]  Loss: {loss.item():.6f}  Time: {forward_time*1000:.2f} ms")

    print()
    print("Training complete!")
    print()

    # Test inference
    print("Testing inference...")
    model.eval()
    with torch.no_grad():
        test_input = torch.randn(1, input_size)
        start_time = time.perf_counter()
        test_output = model(test_input)
        inference_time = time.perf_counter() - start_time

    print(f"  Input shape: {test_input.shape}")
    print(f"  Output shape: {test_output.shape}")
    print(f"  Output values: {test_output[0, :5]}")  # First 5 outputs
    print(f"  Inference time: {inference_time*1000:.2f} ms")
    print()

    # Compare with standard PyTorch
    print("Comparing with standard PyTorch model...")
    pytorch_model = torch.nn.Sequential(
        torch.nn.Linear(input_size, hidden_size),
        torch.nn.ReLU(),
        torch.nn.Linear(hidden_size, hidden_size // 2),
        torch.nn.ReLU(),
        torch.nn.Linear(hidden_size // 2, output_size)
    )

    # Time PyTorch forward pass
    with torch.no_grad():
        start_time = time.perf_counter()
        pytorch_output = pytorch_model(test_input)
        pytorch_time = time.perf_counter() - start_time

    print(f"  PyTorch inference time: {pytorch_time*1000:.2f} ms")
    print(f"  Hologram inference time: {inference_time*1000:.2f} ms")
    if pytorch_time > inference_time:
        speedup = pytorch_time / inference_time
        print(f"  Speedup: {speedup:.2f}x faster")
    else:
        slowdown = inference_time / pytorch_time
        print(f"  Slowdown: {slowdown:.2f}x slower (expected for small models)")
    print()

    print("=" * 60)
    print("Example completed successfully!")
    print("=" * 60)


if __name__ == "__main__":
    main()
