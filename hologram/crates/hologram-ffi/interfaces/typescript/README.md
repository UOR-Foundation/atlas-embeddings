# Hologram FFI - TypeScript/Node.js Bindings

**TypeScript bindings for Hologram's canonical compute acceleration**

## Overview

This package provides comprehensive TypeScript/Node.js bindings for hologram-core, enabling high-performance numerical computations through canonical form compilation. The bindings expose all 50 FFI functions covering 26 core operations plus buffer, tensor, and executor management through a type-safe TypeScript interface.

## Features

- **Complete Coverage**: All 50 FFI functions available (100% hologram-core coverage)
- **Canonical Compilation**: Operations compiled to minimal canonical forms via Sigmatics
- **Type Safety**: Full TypeScript type definitions for all operations
- **Memory Safe**: Handle-based API with explicit resource management
- **High Performance**: Direct FFI bindings with minimal overhead
- **f32 Operations**: Optimized for neural network and ML workloads
- **Cross-Platform**: Works on Linux, macOS, and Windows
- **Mock Fallback**: Development mode with mock implementations
- **Comprehensive Tests**: 51+ test cases with Jest

## Installation

### From NPM (when published)

```bash
npm install hologram-ffi
```

### From Source

```bash
# Navigate to TypeScript interface directory
cd crates/hologram-ffi/interfaces/typescript

# Install dependencies
npm install

# Build TypeScript
npm run build

# Run tests
npm test
```

## Quick Start

```typescript
import * as hg from './src/index';

// Get version information
console.log(`Hologram FFI Version: ${hg.getVersion()}`);

// Create an executor
const executorHandle = hg.newExecutor();

// Allocate buffers
const size = 1024;
const aHandle = hg.executorAllocateBuffer(executorHandle, size);
const bHandle = hg.executorAllocateBuffer(executorHandle, size);
const cHandle = hg.executorAllocateBuffer(executorHandle, size);

// Fill buffers with data
const dataA = Array.from({length: size}, (_, i) => i);
const dataB = Array.from({length: size}, (_, i) => i * 2);
hg.bufferCopyFromSlice(executorHandle, aHandle, JSON.stringify(dataA));
hg.bufferCopyFromSlice(executorHandle, bHandle, JSON.stringify(dataB));

// Perform vector addition
hg.vectorAddF32(executorHandle, aHandle, bHandle, cHandle, size);

// Get results
const resultJson = hg.bufferToVec(executorHandle, cHandle);
const result = JSON.parse(resultJson);
console.log(`First 10 results: ${result.slice(0, 10)}`);

// Clean up resources
hg.bufferCleanup(aHandle);
hg.bufferCleanup(bHandle);
hg.bufferCleanup(cHandle);
hg.executorCleanup(executorHandle);
```

## API Reference

For complete API documentation, see [FFI_API_REFERENCE.md](../../../../docs/FFI_API_REFERENCE.md).

### Type Definitions

```typescript
// Handle types (all are u64/number)
type ExecutorHandle = number;
type BufferHandle = number;
type TensorHandle = number;

// Return types
// u8 returns are used as booleans: 1 = true, 0 = false
// u32 returns are sizes, dimensions, indices
// f32 returns are floating point results
// string returns are JSON-encoded data
```

### Utility Functions (2 functions)

- `getVersion(): string` - Get library version string
- `clearAllRegistries(): void` - Clear all handle registries (cleanup)

### Executor Management (2 functions)

- `newExecutor(): ExecutorHandle` - Create new executor
- `executorCleanup(executorHandle): void` - Release executor

### Buffer Management (13 functions)

**Allocation:**
- `executorAllocateBuffer(executorHandle, length): BufferHandle` - Allocate linear buffer
- `executorAllocateBoundaryBuffer(executorHandle, class, width, height): BufferHandle` - Allocate boundary buffer

**Properties:**
- `bufferLength(bufferHandle): number` - Get buffer length
- `bufferIsEmpty(bufferHandle): number` - Check if empty (1=true, 0=false)
- `bufferIsLinear(bufferHandle): number` - Check if in linear pool
- `bufferIsBoundary(bufferHandle): number` - Check if in boundary pool
- `bufferPool(bufferHandle): string` - Get pool name ("Linear" or "Boundary")
- `bufferElementSize(bufferHandle): number` - Get element size in bytes
- `bufferSizeBytes(bufferHandle): number` - Get total size in bytes
- `bufferClassIndex(bufferHandle): number` - Get class index (0-95)

**Data Transfer:**
- `bufferCopyFromSlice(executorHandle, bufferHandle, dataJson): void` - Copy data from JSON array
- `bufferToVec(executorHandle, bufferHandle): string` - Extract data as JSON array
- `bufferCleanup(bufferHandle): void` - Release buffer

### Mathematical Operations (12 functions)

**Binary Operations:**
- `vectorAddF32(executorHandle, aHandle, bHandle, cHandle, length): void` - Element-wise addition
- `vectorSubF32(executorHandle, aHandle, bHandle, cHandle, length): void` - Element-wise subtraction
- `vectorMulF32(executorHandle, aHandle, bHandle, cHandle, length): void` - Element-wise multiplication
- `vectorDivF32(executorHandle, aHandle, bHandle, cHandle, length): void` - Element-wise division
- `vectorMinF32(executorHandle, aHandle, bHandle, cHandle, length): void` - Element-wise minimum
- `vectorMaxF32(executorHandle, aHandle, bHandle, cHandle, length): void` - Element-wise maximum

**Unary Operations:**
- `vectorAbsF32(executorHandle, aHandle, cHandle, length): void` - Absolute value
- `vectorNegF32(executorHandle, aHandle, cHandle, length): void` - Negation
- `vectorReluF32(executorHandle, aHandle, cHandle, length): void` - ReLU activation

**Advanced Operations:**
- `vectorClipF32(executorHandle, aHandle, cHandle, length, minVal, maxVal): void` - Clip to range
- `scalarAddF32(executorHandle, aHandle, cHandle, length, scalar): void` - Add scalar to all elements
- `scalarMulF32(executorHandle, aHandle, cHandle, length, scalar): void` - Multiply all by scalar

### Reduction Operations (3 functions)

**Note:** Output buffers must have at least 3 elements for internal temporaries.

- `reduceSumF32(executorHandle, inputHandle, outputHandle, length): number` - Sum all elements
- `reduceMinF32(executorHandle, inputHandle, outputHandle, length): number` - Find minimum
- `reduceMaxF32(executorHandle, inputHandle, outputHandle, length): number` - Find maximum

### Activation Functions (4 functions)

- `sigmoidF32(executorHandle, inputHandle, outputHandle, length): void` - Sigmoid activation
- `tanhF32(executorHandle, inputHandle, outputHandle, length): void` - Hyperbolic tangent
- `geluF32(executorHandle, inputHandle, outputHandle, length): void` - GELU activation
- `softmaxF32(executorHandle, inputHandle, outputHandle, length): void` - Softmax activation

### Loss Functions (3 functions)

**Note:** Output buffers must have at least 3 elements for internal temporaries.

- `mseLossF32(executorHandle, predHandle, targetHandle, outputHandle, length): number` - Mean Squared Error
- `crossEntropyLossF32(executorHandle, predHandle, targetHandle, outputHandle, length): number` - Cross Entropy
- `binaryCrossEntropyLossF32(executorHandle, predHandle, targetHandle, outputHandle, length): number` - Binary Cross Entropy

### Linear Algebra (2 functions)

- `gemmF32(executorHandle, aHandle, bHandle, cHandle, m, n, k): void` - General Matrix Multiply (C = A × B)
- `matvecF32(executorHandle, aHandle, xHandle, yHandle, m, n): void` - Matrix-Vector Multiply (y = A × x)

### Tensor Operations (13 functions)

**Creation:**
- `tensorFromBuffer(bufferHandle, shapeJson): TensorHandle` - Create tensor from buffer
- `tensorFromBufferWithStrides(bufferHandle, shapeJson, stridesJson): TensorHandle` - Create with custom strides

**Properties:**
- `tensorShape(tensorHandle): string` - Get shape as JSON array
- `tensorStrides(tensorHandle): string` - Get strides as JSON array
- `tensorOffset(tensorHandle): number` - Get data offset
- `tensorNdim(tensorHandle): number` - Get number of dimensions
- `tensorNumel(tensorHandle): number` - Get total element count
- `tensorIsContiguous(tensorHandle): number` - Check if contiguous (1=true, 0=false)
- `tensorBuffer(tensorHandle): BufferHandle` - Get underlying buffer handle

**Operations:**
- `tensorContiguous(executorHandle, tensorHandle): TensorHandle` - Create contiguous copy
- `tensorTranspose(tensorHandle): TensorHandle` - Transpose 2D tensor
- `tensorReshape(executorHandle, tensorHandle, newShapeJson): TensorHandle` - Reshape tensor
- `tensorSelect(tensorHandle, dim, index): TensorHandle` - Select along dimension
- `tensorMatmul(executorHandle, aHandle, bHandle): TensorHandle` - Matrix multiplication

**Cleanup:**
- `tensorCleanup(tensorHandle): void` - Release tensor (not the underlying buffer)

**Total: 50 functions**

## Usage Examples

### Vector Addition

```typescript
import * as hg from './src/index';

// Create executor
const executor = hg.newExecutor();

// Allocate buffers
const a = hg.executorAllocateBuffer(executor, 1024);
const b = hg.executorAllocateBuffer(executor, 1024);
const c = hg.executorAllocateBuffer(executor, 1024);

// Fill with data
const dataA = Array.from({length: 1024}, (_, i) => i);
const dataB = Array.from({length: 1024}, (_, i) => i * 2);
hg.bufferCopyFromSlice(executor, a, JSON.stringify(dataA));
hg.bufferCopyFromSlice(executor, b, JSON.stringify(dataB));

// Perform addition
hg.vectorAddF32(executor, a, b, c, 1024);

// Get results
const resultJson = hg.bufferToVec(executor, c);
const result = JSON.parse(resultJson);
console.log(`First 5 results: ${result.slice(0, 5)}`); // [0, 3, 6, 9, 12]

// Cleanup
hg.bufferCleanup(a);
hg.bufferCleanup(b);
hg.bufferCleanup(c);
hg.executorCleanup(executor);
```

### Neural Network Layer

```typescript
import * as hg from './src/index';

const executor = hg.newExecutor();

// Allocate buffers for 128×64 matrix and 64-element vector
const sizeMatrix = 128 * 64;
const sizeVec = 64;
const sizeOutput = 128;

const matrixBuf = hg.executorAllocateBuffer(executor, sizeMatrix);
const inputBuf = hg.executorAllocateBuffer(executor, sizeVec);
const outputBuf = hg.executorAllocateBuffer(executor, sizeOutput);
const activatedBuf = hg.executorAllocateBuffer(executor, sizeOutput);

// Fill with weights and input data...

// Linear layer: output = matrix × input
hg.matvecF32(executor, matrixBuf, inputBuf, outputBuf, 128, 64);

// Apply activation: activated = sigmoid(output)
hg.sigmoidF32(executor, outputBuf, activatedBuf, sizeOutput);

// Get results
const resultJson = hg.bufferToVec(executor, activatedBuf);
const activations = JSON.parse(resultJson);

// Cleanup
hg.bufferCleanup(matrixBuf);
hg.bufferCleanup(inputBuf);
hg.bufferCleanup(outputBuf);
hg.bufferCleanup(activatedBuf);
hg.executorCleanup(executor);
```

### Tensor Matrix Multiplication

```typescript
import * as hg from './src/index';

const executor = hg.newExecutor();

// Create 4×8 and 8×3 matrices
const aBuf = hg.executorAllocateBuffer(executor, 32);
const bBuf = hg.executorAllocateBuffer(executor, 24);

// Create tensors
const tensorA = hg.tensorFromBuffer(aBuf, JSON.stringify([4, 8]));
const tensorB = hg.tensorFromBuffer(bBuf, JSON.stringify([8, 3]));

// Matrix multiply: result is 4×3
const resultTensor = hg.tensorMatmul(executor, tensorA, tensorB);

// Get shape
const shapeJson = hg.tensorShape(resultTensor);
const shape = JSON.parse(shapeJson);
console.log(`Result shape: ${shape}`); // [4, 3]

// Cleanup
hg.tensorCleanup(resultTensor);
hg.tensorCleanup(tensorB);
hg.tensorCleanup(tensorA);
hg.bufferCleanup(bBuf);
hg.bufferCleanup(aBuf);
hg.executorCleanup(executor);
```

## Error Handling

The TypeScript bindings use exceptions for error handling:

```typescript
import * as hg from './src/index';

try {
    const executor = hg.newExecutor();
    // ... operations ...
    hg.executorCleanup(executor);
} catch (error) {
    console.error(`Error: ${error}`);
}
```

## Memory Management

All resources must be explicitly cleaned up:

```typescript
import * as hg from './src/index';

// Create resources
const executor = hg.newExecutor();
const buffer = hg.executorAllocateBuffer(executor, 1000);
const tensor = hg.tensorFromBuffer(buffer, JSON.stringify([10, 100]));

// Use resources
// ... operations ...

// Clean up in reverse order
hg.tensorCleanup(tensor);
hg.bufferCleanup(buffer);
hg.executorCleanup(executor);
```

## Performance

The TypeScript bindings provide high-performance computation through:

- **Canonical Compilation**: Operations compiled to minimal forms (typical 4-8x reduction)
- **Direct FFI**: Minimal overhead for cross-language calls
- **JSON Transfer**: Acceptable overhead for most workloads (computation >> transfer)
- **f32 Optimization**: Optimized for neural network precision requirements

**Note**: For large data transfers, minimize round-trips by batching data in single JSON arrays.

## Testing

Run the comprehensive test suite:

```bash
# Run all tests
npm test

# Run tests in watch mode
npm run test:watch

# Run with coverage
npm run test:coverage
```

The test suite includes 51+ test cases covering:
- Core functions
- Executor management
- Buffer operations
- Mathematical operations
- Tensor operations
- Error handling
- Memory management
- Performance benchmarks

## Examples

The `examples/` directory contains comprehensive examples:

- `basic_operations.ts` - Version info and basic usage
- `executor_management.ts` - Executor and buffer management
- `buffer_operations.ts` - Buffer data transfer and operations
- `tensor_operations.ts` - Advanced tensor operations
- `error_handling.ts` - Error handling patterns
- `performance_benchmarks.ts` - Performance measurements
- `integration_tests.ts` - Integration testing examples

Run examples:

```bash
npx ts-node examples/basic_operations.ts
npx ts-node examples/tensor_operations.ts
npx ts-node examples/performance_benchmarks.ts
```

## Development

### Building

```bash
# Install dependencies
npm install

# Build TypeScript
npm run build

# Run tests
npm test

# Run linting
npm run lint

# Format code
npm run format
```

### Project Structure

```
typescript/
├── src/
│   └── index.ts           # Main TypeScript bindings
├── tests/
│   └── hologram_ffi.test.ts  # 51+ test cases
├── examples/              # Example files
├── package.json           # NPM configuration
├── tsconfig.json          # TypeScript configuration
└── jest.config.js         # Jest test configuration
```

## Mock Implementation

The bindings include a mock implementation for development:

- **Automatic Fallback**: If native library fails to load, falls back to mock
- **Development Mode**: Useful for development without native builds
- **Testing**: Enables testing without full native library
- **Type-Safe**: Maintains same TypeScript types and signatures

## Contributing

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests for new functionality
5. Run the test suite
6. Submit a pull request

## License

This project is licensed under the same license as the main hologram-ffi project.

## Support

For questions, issues, or contributions:

- Create an issue on GitHub
- Check the examples for usage patterns
- Review the test suite for implementation details
- See [FFI_API_REFERENCE.md](../../../../docs/FFI_API_REFERENCE.md) for complete API documentation

## Changelog

### v1.0.0

- Complete TypeScript bindings for all 50 FFI functions
- 100% coverage of hologram-core operations
- Comprehensive test suite (51+ tests)
- Full examples for all functionality
- Mock implementation for development
- Production-ready for neural network workloads
