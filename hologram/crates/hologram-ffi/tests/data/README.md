# Test Data Sets for hologram-ffi
# Standard test vectors for comprehensive testing

## Small Test Vectors (1-10 elements)

### Basic Operations
- **Empty Vector**: `[]` - Tests edge case handling
- **Single Element**: `[1.0]` - Tests single element operations
- **Small Vector**: `[1.0, 2.0, 3.0, 4.0, 5.0]` - Tests basic operations
- **Negative Values**: `[-1.0, -2.0, -3.0]` - Tests negative number handling
- **Zero Values**: `[0.0, 0.0, 0.0]` - Tests zero handling
- **Mixed Values**: `[1.0, -2.0, 0.0, 3.5, -4.2]` - Tests mixed positive/negative/zero

### Buffer Operations
- **Buffer Length 1**: Single element buffer
- **Buffer Length 5**: Small buffer for basic operations
- **Buffer Length 10**: Small buffer for testing

### Tensor Operations
- **1D Tensor**: `[1, 2, 3, 4, 5]` - Shape: `[5]`
- **2D Tensor**: `[[1, 2], [3, 4]]` - Shape: `[2, 2]`
- **3D Tensor**: `[[[1, 2], [3, 4]], [[5, 6], [7, 8]]]` - Shape: `[2, 2, 2]`

## Medium Test Vectors (100-1000 elements)

### Vector Operations
- **Vector 100**: `[0.0, 0.01, 0.02, ..., 0.99]` - Linear progression
- **Vector 256**: `[sin(i/256 * 2π) for i in range(256)]` - Sine wave
- **Vector 512**: `[random.uniform(-1, 1) for _ in range(512)]` - Random values
- **Vector 1000**: `[i/1000.0 for i in range(1000)]` - Normalized range

### Buffer Operations
- **Buffer 100**: 100-element buffer for medium operations
- **Buffer 256**: 256-element buffer (common size)
- **Buffer 512**: 512-element buffer for testing
- **Buffer 1000**: 1000-element buffer for comprehensive testing

### Tensor Operations
- **Matrix 10x10**: 100-element 2D tensor
- **Matrix 16x16**: 256-element 2D tensor
- **Matrix 32x32**: 1024-element 2D tensor
- **3D Tensor 8x8x8**: 512-element 3D tensor

## Large Test Vectors (10K-100K elements)

### Vector Operations
- **Vector 10K**: `[sin(i/10000 * 2π) for i in range(10000)]` - Large sine wave
- **Vector 50K**: `[random.uniform(-1, 1) for _ in range(50000)]` - Large random
- **Vector 100K**: `[i/100000.0 for i in range(100000)]` - Large normalized range

### Buffer Operations
- **Buffer 10K**: 10,000-element buffer for large operations
- **Buffer 50K**: 50,000-element buffer for performance testing
- **Buffer 100K**: 100,000-element buffer for stress testing

### Tensor Operations
- **Matrix 100x100**: 10,000-element 2D tensor
- **Matrix 224x224**: 50,176-element 2D tensor (common ML size)
- **Matrix 512x512**: 262,144-element 2D tensor
- **3D Tensor 64x64x64**: 262,144-element 3D tensor

## Edge Case Vectors

### Boundary Conditions
- **Empty Vector**: `[]` - Zero elements
- **Single Element**: `[42.0]` - One element
- **Two Elements**: `[1.0, 2.0]` - Minimum for some operations
- **Max Size**: Platform-dependent maximum size

### Special Values
- **Infinity**: `[float('inf'), float('-inf')]` - Infinity handling
- **NaN**: `[float('nan')]` - Not a Number handling
- **Very Small**: `[1e-10, 1e-20]` - Near-zero values
- **Very Large**: `[1e10, 1e20]` - Large magnitude values

### Data Types
- **f32 Values**: Standard 32-bit float values
- **f64 Values**: Double precision values
- **Integer-like**: `[1.0, 2.0, 3.0]` - Integer values as floats
- **Decimal**: `[1.5, 2.7, 3.14]` - Decimal values

## Test Data Files

### JSON Format
```json
{
    "name": "small_vector_5",
    "description": "5-element test vector",
    "data": [1.0, 2.0, 3.0, 4.0, 5.0],
    "expected_results": {
        "sum": 15.0,
        "mean": 3.0,
        "max": 5.0,
        "min": 1.0
    }
}
```

### Binary Format
- **f32 Binary**: Raw 32-bit float binary data
- **f64 Binary**: Raw 64-bit float binary data
- **Little Endian**: Standard little-endian format
- **Big Endian**: Big-endian format for cross-platform testing

## Usage Examples

### Python
```python
import json
import numpy as np

# Load test data
with open('tests/data/small_vector_5.json', 'r') as f:
    test_data = json.load(f)

# Use in tests
vector = test_data['data']
expected_sum = test_data['expected_results']['sum']
```

### Rust
```rust
use serde_json;

// Load test data
let test_data: serde_json::Value = serde_json::from_str(&std::fs::read_to_string("tests/data/small_vector_5.json")?)?;
let vector: Vec<f32> = test_data["data"].as_array().unwrap().iter().map(|v| v.as_f64().unwrap() as f32).collect();
```

### TypeScript
```typescript
import * as fs from 'fs';

// Load test data
const testData = JSON.parse(fs.readFileSync('tests/data/small_vector_5.json', 'utf8'));
const vector = testData.data;
const expectedSum = testData.expected_results.sum;
```

## Test Data Generation

### Python Generator
```python
import json
import random
import math

def generate_test_vectors():
    """Generate comprehensive test vectors"""
    
    # Small vectors
    small_vectors = {
        "empty": [],
        "single": [1.0],
        "small_5": [1.0, 2.0, 3.0, 4.0, 5.0],
        "negative": [-1.0, -2.0, -3.0],
        "zeros": [0.0, 0.0, 0.0],
        "mixed": [1.0, -2.0, 0.0, 3.5, -4.2]
    }
    
    # Medium vectors
    medium_vectors = {
        "linear_100": [i/100.0 for i in range(100)],
        "sine_256": [math.sin(i/256 * 2 * math.pi) for i in range(256)],
        "random_512": [random.uniform(-1, 1) for _ in range(512)],
        "normalized_1000": [i/1000.0 for i in range(1000)]
    }
    
    # Large vectors
    large_vectors = {
        "sine_10k": [math.sin(i/10000 * 2 * math.pi) for i in range(10000)],
        "random_50k": [random.uniform(-1, 1) for _ in range(50000)],
        "normalized_100k": [i/100000.0 for i in range(100000)]
    }
    
    return {**small_vectors, **medium_vectors, **large_vectors}

# Generate and save test data
test_vectors = generate_test_vectors()
for name, data in test_vectors.items():
    test_case = {
        "name": name,
        "data": data,
        "length": len(data),
        "sum": sum(data) if data else 0,
        "mean": sum(data)/len(data) if data else 0,
        "max": max(data) if data else 0,
        "min": min(data) if data else 0
    }
    
    with open(f'tests/data/{name}.json', 'w') as f:
        json.dump(test_case, f, indent=2)
```

This comprehensive test data structure ensures thorough testing of all hologram-ffi functionality across different data sizes, types, and edge cases.
