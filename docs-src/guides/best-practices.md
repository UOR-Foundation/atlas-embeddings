---
layout: default
title: Best Practices
sidebar: guides
---

# Best Practices

This guide provides recommended usage patterns, performance optimization techniques, and security considerations for the UOR Prime Structure FFI.

## Choosing the Right Implementation

### Pure vs. FFI Runtime Decision Tree

```
Start Here
│
├─ Need mathematical verification? ──Yes──> Use Lean Runtime (FFI)
│
├─ High-frequency operations (>1M/sec)? ──Yes──> Use Pure Implementation
│
├─ Complex mathematical operations? ──Yes──> Consider Lean Runtime
│
├─ Simple deployment requirements? ──Yes──> Use Pure Implementation
│
└─ Default ──────────────────────────────> Use Pure Implementation
```

### Implementation Comparison

| Aspect | Pure Implementation | Lean Runtime (FFI) |
|--------|-------------------|--------------------|
| Performance | 10-15x faster for simple ops | Slower due to FFI overhead |
| Verification | No formal proofs | Mathematically verified |
| Dependencies | None | Requires Lean runtime |
| Deployment | Simple | Complex |
| Memory Usage | Lower | Higher |
| Maintenance | Language-specific | Single source |

## Performance Best Practices

### 1. Minimize FFI Calls

**Bad:**
```go
// Multiple FFI calls in loop
for i := 0; i < 1000000; i++ {
    result := uor.R96Classify(byte(i % 256)) // FFI call each iteration
    process(result)
}
```

**Good:**
```go
// Batch processing
input := make([]byte, 1000000)
for i := range input {
    input[i] = byte(i % 256)
}
results := uor.R96ClassifyBatch(input) // Single FFI call
for _, result := range results {
    process(result)
}
```

### 2. Cache Constants

**Bad:**
```python
# Repeated constant access
for page in range(uor.get_pages()):  # FFI call every iteration
    for byte_val in range(uor.get_bytes()):  # Another FFI call
        process(page, byte_val)
```

**Good:**
```python
# Cache constants once
PAGES = uor.get_pages()
BYTES = uor.get_bytes()

for page in range(PAGES):
    for byte_val in range(BYTES):
        process(page, byte_val)
```

### 3. Use Language-Specific Optimizations

#### Go: Leverage Slices and Channels
```go
func ProcessConcurrently(data []byte, workers int) []byte {
    input := make(chan []byte, workers)
    output := make(chan []byte, workers)
    results := make([]byte, len(data))
    
    // Start workers
    for i := 0; i < workers; i++ {
        go func() {
            for chunk := range input {
                processed := uor.R96ClassifyBatch(chunk)
                output <- processed
            }
        }()
    }
    
    // Distribute work
    chunkSize := len(data) / workers
    for i := 0; i < len(data); i += chunkSize {
        end := min(i+chunkSize, len(data))
        input <- data[i:end]
    }
    close(input)
    
    // Collect results
    for i := 0; i < workers; i++ {
        result := <-output
        copy(results[i*chunkSize:], result)
    }
    
    return results
}
```

#### Python: NumPy Integration
```python
import numpy as np
import uor

def process_large_dataset(data):
    """Efficient processing of large datasets."""
    # Convert to NumPy array for vectorization
    np_data = np.asarray(data, dtype=np.uint8)
    
    # Use pure NumPy implementation for best performance
    if hasattr(uor, 'r96_classify_vectorized'):
        return uor.r96_classify_vectorized(np_data)
    
    # Fallback to chunked processing
    chunk_size = 10000
    results = np.empty_like(np_data)
    
    for i in range(0, len(np_data), chunk_size):
        chunk = np_data[i:i + chunk_size]
        results[i:i + chunk_size] = uor.r96_classify_batch(chunk)
    
    return results
```

#### Rust: Zero-Copy and SIMD
```rust
use std::simd::*;

fn process_simd_optimized(data: &[u8]) -> Vec<u8> {
    let mut results = vec![0u8; data.len()];
    
    // Process 64 bytes at a time with SIMD
    let simd_chunks = data.chunks_exact(64);
    let mut result_chunks = results.chunks_exact_mut(64);
    
    for (input_chunk, output_chunk) in simd_chunks.zip(&mut result_chunks) {
        // SIMD processing here
        for (i, &byte) in input_chunk.iter().enumerate() {
            output_chunk[i] = uor::r96_classify_pure(byte);
        }
    }
    
    // Handle remainder
    let remainder_start = data.len() - (data.len() % 64);
    for (i, &byte) in data[remainder_start..].iter().enumerate() {
        results[remainder_start + i] = uor::r96_classify_pure(byte);
    }
    
    results
}
```

## Memory Management Best Practices

### 1. Resource Cleanup

**Go:**
```go
func ProcessWithCleanup() error {
    if err := uor.Initialize(); err != nil {
        return err
    }
    defer uor.Finalize() // Always cleanup
    
    // Your processing here
    return nil
}
```

**Python:**
```python
class UORProcessor:
    def __enter__(self):
        uor.initialize()
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        uor.finalize()
    
    def process(self, data):
        return uor.r96_classify_batch(data)

# Usage
with UORProcessor() as processor:
    result = processor.process(data)
```

**Rust:**
```rust
struct UORProcessor {
    _phantom: std::marker::PhantomData<()>,
}

impl UORProcessor {
    fn new() -> Result<Self, UORError> {
        uor::initialize()?;
        Ok(Self { _phantom: std::marker::PhantomData })
    }
}

impl Drop for UORProcessor {
    fn drop(&mut self) {
        uor::finalize();
    }
}
```

### 2. Memory Pool Usage

```go
// Reuse buffers to reduce allocations
type BufferPool struct {
    pool sync.Pool
}

func NewBufferPool() *BufferPool {
    return &BufferPool{
        pool: sync.Pool{
            New: func() interface{} {
                return make([]byte, 0, 1024)
            },
        },
    }
}

func (bp *BufferPool) Get() []byte {
    return bp.pool.Get().([]byte)
}

func (bp *BufferPool) Put(buf []byte) {
    bp.pool.Put(buf[:0])
}
```

## Error Handling Patterns

### 1. Comprehensive Error Checking

**Go:**
```go
func SafeR96Classify(b byte) (byte, error) {
    if !uor.IsInitialized() {
        return 0, errors.New("UOR not initialized")
    }
    
    result := uor.R96Classify(b)
    if result >= 96 {
        return 0, fmt.Errorf("invalid R96 class: %d", result)
    }
    
    return result, nil
}
```

**Rust:**
```rust
#[derive(Debug, thiserror::Error)]
pub enum UORError {
    #[error("UOR not initialized")]
    NotInitialized,
    #[error("Invalid R96 class: {0}")]
    InvalidR96Class(u8),
    #[error("Invalid coordinate: page={page}, byte={byte}")]
    InvalidCoordinate { page: u8, byte: u8 },
}

pub fn safe_r96_classify(b: u8) -> Result<u8, UORError> {
    if !is_initialized() {
        return Err(UORError::NotInitialized);
    }
    
    let result = r96_classify_pure(b);
    if result >= 96 {
        return Err(UORError::InvalidR96Class(result));
    }
    
    Ok(result)
}
```

### 2. Graceful Degradation

```python
def robust_r96_classify(data):
    """Classify with fallback strategies."""
    try:
        # Try vectorized version first
        return uor.r96_classify_vectorized(data)
    except AttributeError:
        # Fall back to batch processing
        try:
            return uor.r96_classify_batch(data)
        except Exception:
            # Ultimate fallback: individual calls
            return [uor.r96_classify(b) for b in data]
```

## Concurrency and Threading

### 1. Thread Safety

**Go (Goroutine-Safe):**
```go
var (
    initOnce sync.Once
    initErr  error
)

func EnsureInitialized() error {
    initOnce.Do(func() {
        initErr = uor.Initialize()
    })
    return initErr
}

func ConcurrentProcessor(data []byte, numWorkers int) []byte {
    if err := EnsureInitialized(); err != nil {
        panic(err)
    }
    
    // Worker pool implementation
    // ... (see previous example)
}
```

**Rust (Send + Sync):**
```rust
use std::sync::{Arc, Mutex, Once};
use std::thread;

static INIT: Once = Once::new();
static mut INIT_RESULT: Result<(), UORError> = Ok(());

fn ensure_initialized() -> Result<(), UORError> {
    unsafe {
        INIT.call_once(|| {
            INIT_RESULT = uor::initialize();
        });
        INIT_RESULT.clone()
    }
}

fn concurrent_process(data: Vec<u8>, num_threads: usize) -> Vec<u8> {
    ensure_initialized().expect("Failed to initialize");
    
    let data = Arc::new(data);
    let chunk_size = data.len() / num_threads;
    
    let handles: Vec<_> = (0..num_threads)
        .map(|i| {
            let data = Arc::clone(&data);
            let start = i * chunk_size;
            let end = if i == num_threads - 1 { data.len() } else { (i + 1) * chunk_size };
            
            thread::spawn(move || {
                data[start..end]
                    .iter()
                    .map(|&b| uor::r96_classify_pure(b))
                    .collect::<Vec<u8>>()
            })
        })
        .collect();
    
    handles
        .into_iter()
        .flat_map(|h| h.join().unwrap())
        .collect()
}
```

## Security Considerations

### 1. Input Validation

```c
// C: Validate inputs at FFI boundary
uint8_t safe_phi_page(uint32_t code) {
    uint8_t page = (code >> 8) & 0xFF;
    // Ensure page is in valid range
    return page % 48;
}

uint8_t safe_phi_byte(uint32_t code) {
    // Byte extraction is inherently safe (8 bits)
    return code & 0xFF;
}
```

```python
# Python: Comprehensive validation
def validate_coordinate(page, byte_val):
    if not isinstance(page, int) or not (0 <= page < 48):
        raise ValueError(f"Page must be integer 0-47, got {page}")
    if not isinstance(byte_val, int) or not (0 <= byte_val < 256):
        raise ValueError(f"Byte must be integer 0-255, got {byte_val}")
```

### 2. Bounds Checking

```rust
pub fn safe_phi_encode(page: u8, byte: u8) -> Result<u32, UORError> {
    if page >= 48 {
        return Err(UORError::InvalidCoordinate {
            page,
            byte,
        });
    }
    
    // Byte is inherently valid (u8 range)
    Ok(phi_encode_unchecked(page, byte))
}
```

## Testing Best Practices

### 1. Property-Based Testing

```go
func TestR96Properties(t *testing.T) {
    quick.Check(func(b byte) bool {
        class := uor.R96Classify(b)
        return class < 96
    }, nil)
}

func TestPhiRoundtrip(t *testing.T) {
    quick.Check(func(page, byteVal uint8) bool {
        if page >= 48 {
            return true // Skip invalid inputs
        }
        
        encoded := uor.PhiEncode(page, byteVal)
        decodedPage := uor.PhiPage(encoded)
        decodedByte := uor.PhiByte(encoded)
        
        return decodedPage == page && decodedByte == byteVal
    }, nil)
}
```

### 2. Benchmark-Driven Development

```go
func BenchmarkR96_Current(b *testing.B) {
    for i := 0; i < b.N; i++ {
        uor.R96Classify(byte(i % 256))
    }
}

func BenchmarkR96_Optimized(b *testing.B) {
    for i := 0; i < b.N; i++ {
        uor.R96ClassifyOptimized(byte(i % 256))
    }
}
```

## Deployment Best Practices

### 1. Feature Flags

```go
// Build tags for different implementations
//go:build lean
package uor

func R96Classify(b byte) byte {
    return lean_uor_r96_classify(b) // FFI version
}
```

```go
//go:build !lean
package uor

func R96Classify(b byte) byte {
    return r96ClassifyPure(b) // Pure version
}
```

### 2. Configuration Management

```yaml
# config.yaml
uor:
  runtime: "pure" # or "lean"
  batch_size: 10000
  workers: 4
  enable_simd: true
```

```go
type Config struct {
    Runtime    string `yaml:"runtime"`
    BatchSize  int    `yaml:"batch_size"`
    Workers    int    `yaml:"workers"`
    EnableSIMD bool   `yaml:"enable_simd"`
}

func LoadConfig(path string) (*Config, error) {
    data, err := ioutil.ReadFile(path)
    if err != nil {
        return nil, err
    }
    
    var config Config
    if err := yaml.Unmarshal(data, &config); err != nil {
        return nil, err
    }
    
    return &config, nil
}
```

## Common Anti-Patterns to Avoid

### 1. Excessive FFI Calls
```go
// DON'T: Call FFI in tight loops
for i := 0; i < 1000000; i++ {
    result := uor.R96Classify(byte(i)) // 14ms overhead per call
}

// DO: Batch operations
data := make([]byte, 1000000)
for i := range data { data[i] = byte(i) }
results := uor.R96ClassifyBatch(data) // Single call
```

### 2. Ignoring Resource Management
```python
# DON'T: Forget cleanup
def process_data(data):
    uor.initialize()
    return uor.r96_classify_batch(data)
    # Missing uor.finalize()!

# DO: Use context managers
def process_data(data):
    with uor.UORContext():
        return uor.r96_classify_batch(data)
```

### 3. Assumptions About Thread Safety
```rust
// DON'T: Assume all functions are thread-safe
static GLOBAL_UOR: uor::UORProcessor = uor::UORProcessor::new();

fn bad_concurrent_access() {
    // Multiple threads accessing without synchronization
    GLOBAL_UOR.process(data);
}

// DO: Use proper synchronization
static GLOBAL_UOR: Lazy<Mutex<uor::UORProcessor>> = 
    Lazy::new(|| Mutex::new(uor::UORProcessor::new()));
```

Following these best practices ensures optimal performance, reliability, and maintainability of UOR Prime Structure FFI applications.