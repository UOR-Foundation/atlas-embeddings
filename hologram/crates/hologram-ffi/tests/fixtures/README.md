# Test Fixtures for hologram-ffi
# Reusable test components for comprehensive testing

## Executor Fixtures

### Standard Executor
```rust
// Standard executor for most tests
pub fn create_standard_executor() -> u64 {
    new_executor()
}
```

### Custom Backend Executor
```rust
// Executor with custom backend configuration
pub fn create_custom_executor(backend_type: &str) -> u64 {
    executor_with_backend(backend_type.to_string())
}
```

### Executor with Phase
```rust
// Executor with specific phase setting
pub fn create_executor_with_phase(phase: u16) -> u64 {
    let executor = new_executor();
    executor_advance_phase(executor, phase);
    executor
}
```

## Buffer Fixtures

### Small Linear Buffer
```rust
// 100-element linear buffer
pub fn create_small_linear_buffer(executor: u64) -> u64 {
    executor_allocate_buffer(executor, 100)
}
```

### Medium Linear Buffer
```rust
// 1000-element linear buffer
pub fn create_medium_linear_buffer(executor: u64) -> u64 {
    executor_allocate_buffer(executor, 1000)
}
```

### Large Linear Buffer
```rust
// 10000-element linear buffer
pub fn create_large_linear_buffer(executor: u64) -> u64 {
    executor_allocate_buffer(executor, 10000)
}
```

### Boundary Buffer
```rust
// Boundary buffer with specific parameters
pub fn create_boundary_buffer(executor: u64, class: u8, width: u32, height: u32) -> u64 {
    executor_allocate_boundary_buffer(executor, class, width, height)
}
```

### Standard Boundary Buffer
```rust
// Standard 16x16 boundary buffer
pub fn create_standard_boundary_buffer(executor: u64) -> u64 {
    executor_allocate_boundary_buffer(executor, 0, 16, 16)
}
```

## Tensor Fixtures

### 1D Tensor
```rust
// 1-dimensional tensor from buffer
pub fn create_1d_tensor(buffer: u64, length: u32) -> u64 {
    let shape = format!("[{}]", length);
    tensor_from_buffer(buffer, shape)
}
```

### 2D Tensor
```rust
// 2-dimensional tensor from buffer
pub fn create_2d_tensor(buffer: u64, rows: u32, cols: u32) -> u64 {
    let shape = format!("[{}, {}]", rows, cols);
    tensor_from_buffer(buffer, shape)
}
```

### 3D Tensor
```rust
// 3-dimensional tensor from buffer
pub fn create_3d_tensor(buffer: u64, dim1: u32, dim2: u32, dim3: u32) -> u64 {
    let shape = format!("[{}, {}, {}]", dim1, dim2, dim3);
    tensor_from_buffer(buffer, shape)
}
```

### Tensor with Strides
```rust
// Tensor with custom strides
pub fn create_tensor_with_strides(buffer: u64, shape: &str, strides: &str) -> u64 {
    tensor_from_buffer_with_strides(buffer, shape.to_string(), strides.to_string())
}
```

## Operation Fixtures

### Vector Addition Operation
```rust
// Vector addition with known inputs/outputs
pub fn vector_add_fixture(a: &[f32], b: &[f32]) -> Vec<f32> {
    a.iter().zip(b.iter()).map(|(x, y)| x + y).collect()
}
```

### Matrix Multiplication Operation
```rust
// Matrix multiplication with known inputs/outputs
pub fn matrix_multiply_fixture(a: &[f32], b: &[f32], m: usize, n: usize, k: usize) -> Vec<f32> {
    let mut result = vec![0.0; m * k];
    for i in 0..m {
        for j in 0..k {
            for l in 0..n {
                result[i * k + j] += a[i * n + l] * b[l * k + j];
            }
        }
    }
    result
}
```

### Activation Function Operations
```rust
// Sigmoid activation
pub fn sigmoid_fixture(x: f32) -> f32 {
    1.0 / (1.0 + (-x).exp())
}

// Tanh activation
pub fn tanh_fixture(x: f32) -> f32 {
    x.tanh()
}

// ReLU activation
pub fn relu_fixture(x: f32) -> f32 {
    x.max(0.0)
}
```

## Error Fixtures

### Invalid Handle Error
```rust
// Generate invalid handle for error testing
pub fn create_invalid_handle() -> u64 {
    0xFFFFFFFFFFFFFFFF  // Invalid handle value
}
```

### Invalid Atlas Class Error
```rust
// Generate invalid atlas class for error testing
pub fn create_invalid_atlas_class() -> u8 {
    255  // Invalid class (must be < 96)
}
```

### Memory Allocation Error
```rust
// Attempt to allocate extremely large buffer
pub fn create_memory_allocation_error(executor: u64) -> u64 {
    executor_allocate_buffer(executor, u32::MAX)  // Should fail
}
```

## Test Data Fixtures

### Small Test Vector
```json
{
    "name": "small_vector",
    "data": [1.0, 2.0, 3.0, 4.0, 5.0],
    "expected_sum": 15.0,
    "expected_mean": 3.0,
    "expected_max": 5.0,
    "expected_min": 1.0
}
```

### Medium Test Vector
```json
{
    "name": "medium_vector",
    "data": [i/100.0 for i in range(100)],
    "expected_sum": 49.5,
    "expected_mean": 0.495,
    "expected_max": 0.99,
    "expected_min": 0.0
}
```

### Large Test Vector
```json
{
    "name": "large_vector",
    "data": [i/1000.0 for i in range(1000)],
    "expected_sum": 499.5,
    "expected_mean": 0.4995,
    "expected_max": 0.999,
    "expected_min": 0.0
}
```

## Performance Fixtures

### Benchmark Data
```rust
// Large dataset for performance testing
pub fn create_benchmark_data(size: usize) -> Vec<f32> {
    (0..size).map(|i| (i as f32) / (size as f32)).collect()
}
```

### Memory Usage Fixture
```rust
// Measure memory usage
pub fn measure_memory_usage<F>(f: F) -> usize 
where 
    F: FnOnce() -> ()
{
    // Implementation would measure memory before/after
    // This is a placeholder for actual memory measurement
    0
}
```

## Cross-Language Fixtures

### Python Test Fixture
```python
import hologram_ffi as hg

def create_test_executor():
    """Create a test executor"""
    return hg.new_executor()

def create_test_buffer(executor_handle, size=1000):
    """Create a test buffer"""
    return hg.executor_allocate_buffer(executor_handle, size)

def cleanup_test_resources(executor_handle, buffer_handle):
    """Clean up test resources"""
    hg.buffer_cleanup(buffer_handle)
    hg.executor_cleanup(executor_handle)
```

### TypeScript Test Fixture
```typescript
import {
    new_executor,
    executor_allocate_buffer,
    buffer_cleanup,
    executor_cleanup
} from "hologram-ffi";

export function createTestExecutor(): number {
    return new_executor();
}

export function createTestBuffer(executorHandle: number, size: number = 1000): number {
    return executor_allocate_buffer(executorHandle, size);
}

export function cleanupTestResources(executorHandle: number, bufferHandle: number): void {
    buffer_cleanup(bufferHandle);
    executor_cleanup(executorHandle);
}
```

## Usage Examples

### Rust Test with Fixtures
```rust
#[test]
fn test_buffer_operations_with_fixtures() {
    let executor = create_standard_executor();
    let buffer = create_medium_linear_buffer(executor);
    
    // Test operations
    buffer_fill(buffer, 1.5, 1000);
    let length = buffer_length(buffer);
    assert_eq!(length, 1000);
    
    // Cleanup
    buffer_cleanup(buffer);
    executor_cleanup(executor);
}
```

### Python Test with Fixtures
```python
def test_buffer_operations_with_fixtures():
    executor = create_test_executor()
    buffer = create_test_buffer(executor, 1000)
    
    try:
        # Test operations
        hg.buffer_fill(buffer, 1.5, 1000)
        length = hg.buffer_length(buffer)
        assert length == 1000
    finally:
        cleanup_test_resources(executor, buffer)
```

### TypeScript Test with Fixtures
```typescript
describe("Buffer Operations with Fixtures", () => {
    test("should perform buffer operations", () => {
        const executor = createTestExecutor();
        const buffer = createTestBuffer(executor, 1000);
        
        try {
            // Test operations
            buffer_fill(buffer, 1.5, 1000);
            const length = buffer_length(buffer);
            expect(length).toBe(1000);
        } finally {
            cleanupTestResources(executor, buffer);
        }
    });
});
```

## Fixture Management

### Fixture Registry
```rust
// Global fixture registry for test management
use std::collections::HashMap;

pub struct FixtureRegistry {
    executors: HashMap<String, u64>,
    buffers: HashMap<String, u64>,
    tensors: HashMap<String, u64>,
}

impl FixtureRegistry {
    pub fn new() -> Self {
        Self {
            executors: HashMap::new(),
            buffers: HashMap::new(),
            tensors: HashMap::new(),
        }
    }
    
    pub fn register_executor(&mut self, name: &str, handle: u64) {
        self.executors.insert(name.to_string(), handle);
    }
    
    pub fn get_executor(&self, name: &str) -> Option<u64> {
        self.executors.get(name).copied()
    }
    
    pub fn cleanup_all(&mut self) {
        // Cleanup all registered resources
        for (_, handle) in self.executors.drain() {
            executor_cleanup(handle);
        }
        for (_, handle) in self.buffers.drain() {
            buffer_cleanup(handle);
        }
        for (_, handle) in self.tensors.drain() {
            tensor_cleanup(handle);
        }
    }
}
```

This comprehensive fixture system provides reusable components for all types of testing scenarios in hologram-ffi, ensuring consistent and maintainable test code across all language interfaces.
