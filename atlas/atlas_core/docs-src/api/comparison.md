---
layout: default
title: API Comparison
sidebar: api
---

# API Comparison Across Languages

This page provides a comprehensive comparison of the UOR Prime Structure FFI APIs across all supported languages, showing equivalent functionality and usage patterns.

## Function Mapping Table

| Function Category | C FFI | Go | Python | Rust | Node.js |
|------------------|-------|----|---------|----- |--------|
| **Initialization** | `lean_uor_initialize()` | `uor.Initialize()` | `uor.initialize()` | `uor::initialize()` | `uor.initialize()` |
| **Cleanup** | `lean_uor_finalize()` | `uor.Finalize()` | `uor.finalize()` | `uor::finalize()` | `uor.finalize()` |
| **Pages** | `lean_uor_pages()` | `uor.GetPages()` | `uor.get_pages()` | `uor::get_pages()` | `uor.getPages()` |
| **Bytes** | `lean_uor_bytes()` | `uor.GetBytes()` | `uor.get_bytes()` | `uor::get_bytes()` | `uor.getBytes()` |
| **R-Classes** | `lean_uor_rclasses()` | `uor.GetRClasses()` | `uor.get_rclasses()` | `uor::get_rclasses()` | `uor.getRClasses()` |
| **ABI Version** | `lean_uor_abi_version()` | `uor.GetABIVersion()` | `uor.get_abi_version()` | `uor::get_abi_version()` | `uor.getABIVersion()` |
| **R96 Classify** | `lean_uor_r96_classify(b)` | `uor.R96Classify(b)` | `uor.r96_classify(b)` | `uor::r96_classify(b)` | `uor.r96Classify(b)` |
| **Φ Encode** | `lean_uor_phi_encode(p, b)` | `uor.PhiEncode(p, b)` | `uor.phi_encode(p, b)` | `uor::phi_encode(p, b)` | `uor.phiEncode(p, b)` |
| **Φ Page** | `lean_uor_phi_page(code)` | `uor.PhiPage(code)` | `uor.phi_page(code)` | `uor::phi_page(code)` | `uor.phiPage(code)` |
| **Φ Byte** | `lean_uor_phi_byte(code)` | `uor.PhiByte(code)` | `uor.phi_byte(code)` | `uor::phi_byte(code)` | `uor.phiByte(code)` |
| **Truth Zero** | `lean_uor_truth_zero(budget)` | `uor.TruthZero(budget)` | `uor.truth_zero(budget)` | `uor::truth_zero(budget)` | `uor.truthZero(budget)` |
| **Truth Add** | `lean_uor_truth_add(a, b)` | `uor.TruthAdd(a, b)` | `uor.truth_add(a, b)` | `uor::truth_add(a, b)` | `uor.truthAdd(a, b)` |

## Type System Comparison

### Basic Types

| Concept | C | Go | Python | Rust | Node.js |
|---------|---|----|---------|----- |--------|
| **Byte** | `uint8_t` | `byte` | `int` (0-255) | `u8` | `number` |
| **32-bit Uint** | `uint32_t` | `uint32` | `int` | `u32` | `number` |
| **32-bit Int** | `int32_t` | `int32` | `int` | `i32` | `number` |
| **Boolean** | `uint8_t` (0/1) | `bool` | `bool` | `bool` | `boolean` |
| **Error** | `int` (return code) | `error` | `Exception` | `Result<T, E>` | `Error` / Promise rejection |

### Runtime API Enhanced Types

| Concept | Go Runtime | Python Runtime | Rust Runtime | Node Runtime |
|---------|------------|----------------|--------------|-------------|
| **Coordinate** | `uorffi.PhiCoordinate` | `uor_runtime.PhiCoordinate` | `uor_runtime::PhiCoordinate` | `PhiCoordinate` |
| **Classifier** | `uorffi.R96Classifier` | `uor_runtime.R96Classifier` | `uor_runtime::R96Classifier` | `R96Classifier` |
| **Processor** | `uorffi.Processor` | `uor_runtime.UORProcessor` | `uor_runtime::Processor` | `UORProcessor` |

## API Usage Patterns

### Initialization and Cleanup

#### C - Manual Management
```c
int result = lean_uor_initialize();
if (result != 0) {
    return result;
}
// ... use UOR functions ...
lean_uor_finalize();
```

#### Go - Defer Pattern  
```go
if err := uor.Initialize(); err != nil {
    return err
}
defer uor.Finalize()
// ... use UOR functions ...
```

#### Python - Context Manager
```python
with uor.UORContext():
    # ... use UOR functions ...
    pass
# Or manual:
uor.initialize()
try:
    # ... use UOR functions ...
finally:
    uor.finalize()
```

#### Rust - RAII
```rust
let _uor = uor::initialize()?; // Returns guard
// ... use UOR functions ...
// Automatic cleanup when guard drops
```

#### Node.js - Async/Await
```javascript
try {
    await uor.initialize();
    // ... use UOR functions ...
} finally {
    uor.finalize();
}
```

### Error Handling Patterns

#### C - Return Codes
```c
uint8_t result = lean_uor_r96_classify(input);
// No explicit error checking needed for valid input
// Function guarantees result < 96
```

#### Go - Error Return
```go
result, err := uor.R96Classify(input)
if err != nil {
    return fmt.Errorf("classification failed: %w", err)
}
```

#### Python - Exceptions
```python
try:
    result = uor.r96_classify(input)
except ValueError as e:
    print(f"Invalid input: {e}")
    return
```

#### Rust - Result Types
```rust
match uor::r96_classify(input) {
    Ok(result) => println!("Classification: {}", result),
    Err(e) => eprintln!("Error: {}", e),
}
```

#### Node.js - Promise/Exception
```javascript
try {
    const result = await uor.r96Classify(input);
    console.log('Classification:', result);
} catch (error) {
    console.error('Error:', error.message);
}
```

## Performance Characteristics

### Basic Operations (per call)

| Operation | C Direct | Go Pure | Go FFI | Python Pure | Python FFI | Rust Pure | Rust FFI | Node Pure | Node FFI |
|-----------|----------|---------|--------|-------------|------------|-----------|----------|-----------|----------|
| Constants | 0.5ns | 0.6ns | 12ns | 45ns | 68ns | 0.5ns | 12ns | 9ns | 23ns |
| R96 Classify | 2.3ns | 1.8ns | 14ns | 52ns | 79ns | 1.6ns | 14ns | 12ns | 29ns |
| Φ Encode | 1.1ns | 1.2ns | 14ns | 49ns | 72ns | 1.0ns | 13ns | 10ns | 26ns |
| Φ Decode | 1.3ns | 1.4ns | 14ns | 51ns | 75ns | 1.2ns | 14ns | 10ns | 27ns |

### Batch Processing (1MB data)

| Language | Pure Implementation | FFI Implementation | Speedup Ratio |
|----------|-------------------|------------------|-------------|
| Go | 556 MB/s | 68 MB/s | 8.2x |
| Python | 1250 MB/s (NumPy) | 12 MB/s | 104x |
| Rust | 833 MB/s | 70 MB/s | 11.9x |
| Node.js | 81 MB/s | 35 MB/s | 2.3x |

## Feature Comparison Matrix

| Feature | Basic API | Go Runtime | Python Runtime | Rust Runtime | Node Runtime |
|---------|-----------|------------|----------------|--------------|-------------|
| **Basic Functions** | ✓ | ✓ | ✓ | ✓ | ✓ |
| **Batch Operations** | ✗ | ✓ | ✓ | ✓ | ✓ |
| **Object-Oriented API** | ✗ | ✓ | ✓ | ✓ | ✓ |
| **Type Safety** | ✗ | Partial | Runtime | ✓ | TypeScript |
| **Memory Safety** | ✗ | ✓ | ✓ | ✓ | ✓ |
| **Async Support** | ✗ | ✓ | ✓ | ✓ | ✓ |
| **Pure Implementation** | ✗ | ✓ | ✓ | ✓ | ✓ |
| **SIMD Optimization** | ✗ | ✗ | NumPy | ✓ | ✗ |
| **Streaming API** | ✗ | ✓ | ✓ | ✓ | ✓ |

## Advanced API Comparison

### Coordinate Objects

#### Go Runtime
```go
type PhiCoordinate struct {
    page, byte uint8
}

func NewPhiCoordinate(page, byte uint8) *PhiCoordinate
func (pc *PhiCoordinate) Encode() uint32
func (pc *PhiCoordinate) Page() uint8
func (pc *PhiCoordinate) Byte() uint8
```

#### Python Runtime
```python
class PhiCoordinate:
    def __init__(self, page: int, byte: int)
    def encode(self) -> int
    @property
    def page(self) -> int
    @property 
    def byte(self) -> int
```

#### Rust Runtime
```rust
pub struct PhiCoordinate {
    page: u8,
    byte: u8,
}

impl PhiCoordinate {
    pub fn new(page: u8, byte: u8) -> Result<Self, UORError>
    pub fn encode(&self) -> u32
    pub fn page(&self) -> u8
    pub fn byte(&self) -> u8
}
```

#### Node.js Runtime
```javascript
class PhiCoordinate {
    constructor(page, byte) // throws on invalid input
    encode() // returns number
    get page() // returns number
    get byte() // returns number
}
```

### Batch Processing APIs

#### Go Runtime
```go
func R96ClassifyBatch(input []byte) ([]byte, error)
func ProcessStream(input <-chan []byte) <-chan []byte
```

#### Python Runtime  
```python
def r96_classify_batch(data: Union[List[int], np.ndarray]) -> np.ndarray
def process_stream(input_stream: Iterator[bytes]) -> Iterator[bytes]
```

#### Rust Runtime
```rust
pub fn r96_classify_batch(input: &[u8]) -> Result<Vec<u8>, UORError>
pub fn process_stream(input: impl Stream<Item = Vec<u8>>) -> impl Stream<Item = Vec<u8>>
```

#### Node.js Runtime
```javascript
async function r96ClassifyBatch(input) // Promise<Uint8Array>
function processStream(inputStream) // Transform stream
```

## Migration Guide

### From Basic to Runtime API

#### Go Migration
```go
// Before (basic)
result := uor.R96Classify(b)

// After (runtime)
processor := uorffi.NewProcessor()
result := processor.ClassifyByte(b)
```

#### Python Migration
```python
# Before (basic)
result = uor.r96_classify(b)

# After (runtime)
with uor_runtime.UORProcessor() as processor:
    result = processor.classify_byte(b)
```

### Cross-Language Data Exchange

All languages use identical binary formats:
- **R96 Classes**: 8-bit unsigned integers (0-95)
- **Φ Codes**: 32-bit unsigned integers (little-endian)
- **Coordinates**: (page, byte) as (u8, u8) tuples
- **Truth Values**: Boolean (true/false)

## Best Practices by Language

### C
- Always check initialization return code
- Call finalize in cleanup handlers
- Validate inputs at application boundary

### Go
- Use defer for cleanup
- Prefer pure implementation for performance
- Use channels for concurrent processing

### Python
- Use context managers for resource management
- Prefer NumPy arrays for batch operations
- Consider pure implementation for CPU-bound tasks

### Rust
- Leverage Result types for error handling
- Use RAII for automatic resource management
- Enable SIMD features for performance

### Node.js
- Use async/await for non-blocking operations
- Prefer streams for large data processing
- Consider Web Workers for CPU-intensive tasks

This comparison enables informed decisions about language choice and API usage patterns for UOR Prime Structure FFI applications.