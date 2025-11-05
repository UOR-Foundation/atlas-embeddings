---
layout: default
title: FFI Design
sidebar: guides
---

# FFI Design and Architecture

The Foreign Function Interface (FFI) layer is a critical component that bridges the verified Lean mathematical core with multiple programming languages. This guide explains the design principles, implementation choices, and trade-offs of the FFI architecture.

## Design Philosophy

The FFI layer serves as an **intermediary specification** rather than an implementation. It defines a protocol that all language bindings follow while allowing multiple runtime choices.

### Key Principles

1. **Protocol, Not Implementation**: The FFI defines *what* functions exist, not *how* they work
2. **Runtime Flexibility**: Each language can choose between Lean runtime or pure implementations
3. **ABI Stability**: C-compatible interface ensures long-term compatibility
4. **Zero-Copy Where Possible**: Minimize data copying across language boundaries
5. **Mathematical Fidelity**: Preserve verified properties from Lean core

## FFI Interface Specification

### Function Categories

The FFI exposes several categories of functions:

```c
// System Management
uint32_t lean_uor_abi_version(void);
int      lean_uor_initialize(void);
void     lean_uor_finalize(void);

// Constants
uint32_t lean_uor_pages(void);        // 48
uint32_t lean_uor_bytes(void);        // 256  
uint32_t lean_uor_rclasses(void);     // 96

// R96 Resonance Classifier
uint8_t  lean_uor_r96_classify(uint8_t b);

// Φ Boundary Encoding
uint32_t lean_uor_phi_encode(uint8_t page, uint8_t byte);
uint8_t  lean_uor_phi_page(uint32_t code);
uint8_t  lean_uor_phi_byte(uint32_t code);

// Truth ≙ Conservation
uint8_t  lean_uor_truth_zero(int32_t budget);
uint8_t  lean_uor_truth_add(int32_t a, int32_t b);
```

### Data Type Mapping

| Lean Type | C Type | Size | Description |
|-----------|--------|------|-------------|
| `UInt8` | `uint8_t` | 1 byte | Byte values, resonance classes |
| `UInt32` | `uint32_t` | 4 bytes | Φ-encoded coordinates, counts |
| `Int32` | `int32_t` | 4 bytes | Budget values for truth functions |
| `Bool` | `uint8_t` | 1 byte | Truth values (0/1) |

## Runtime Implementation Strategies

### Strategy 1: Lean Runtime (Verified)

Uses the verified Lean implementation through dynamic linking:

```
Application → Language Wrapper → C FFI → Lean Runtime → Verified Math
```

**Advantages:**
- Mathematically verified correctness
- Single source of truth for algorithms
- Access to full Lean theorem proving capabilities
- Consistent behavior across all languages

**Disadvantages:**
- Requires Lean runtime dependencies
- Cross-language call overhead
- Larger memory footprint
- More complex deployment

**Example (Go):**
```go
// #cgo LDFLAGS: -L${SRCDIR}/../.lake/build/lib -lUOR
// #include "uor_ffi.h"
import "C"

func Pages() uint32 {
    return uint32(C.lean_uor_pages()) // Calls verified Lean
}
```

### Strategy 2: Pure Implementation (Optimized)

Implements functions natively in each target language:

```
Application → Language Wrapper → Pure Language Implementation
```

**Advantages:**
- No external dependencies
- Optimal performance for target language
- Simpler deployment and distribution
- Integration with language-specific optimizations

**Disadvantages:**
- Multiple implementations to maintain
- No formal verification guarantees
- Potential behavior differences
- Duplication of mathematical logic

**Example (Go):**
```go
func Pages() uint32 {
    return 48 // Pure Go implementation
}

func R96Classify(b uint8) uint8 {
    // Pure Go implementation of R96 classifier
    return r96ClassificationTable[b]
}
```

### Strategy 3: Hybrid Runtime (Flexible)

Allows runtime selection between Lean and pure implementations:

```go
var useLeanRuntime = os.Getenv("UOR_USE_LEAN") == "1"

func Pages() uint32 {
    if useLeanRuntime {
        return uint32(C.lean_uor_pages()) // Lean
    }
    return 48 // Pure Go
}
```

## Language-Specific FFI Integration

### Go Integration

**CGO Approach:**
```go
package uor

// #cgo LDFLAGS: -L${SRCDIR}/../lib -luor
// #include "uor_ffi.h"
import "C"
import "unsafe"

func R96Classify(b byte) byte {
    return byte(C.lean_uor_r96_classify(C.uint8_t(b)))
}
```

**Build Tags for Runtime Selection:**
```go
//go:build lean
// +build lean

func init() {
    C.lean_uor_initialize()
}
```

### Rust Integration

**Bindgen Approach:**
```rust
// build.rs
extern crate bindgen;

fn main() {
    let bindings = bindgen::Builder::default()
        .header("uor_ffi.h")
        .generate()
        .expect("Unable to generate bindings");
    
    bindings
        .write_to_file("src/bindings.rs")
        .expect("Couldn't write bindings!");
}
```

**Safe Rust Wrapper:**
```rust
use crate::bindings::*;

pub fn r96_classify(b: u8) -> Result<u8, Error> {
    unsafe {
        Ok(lean_uor_r96_classify(b))
    }
}
```

### Python Integration

**ctypes Approach:**
```python
import ctypes
import os

# Load the library
lib_path = os.path.join(os.path.dirname(__file__), 'libuor.so')
_lib = ctypes.CDLL(lib_path)

# Define function signatures
_lib.lean_uor_r96_classify.argtypes = [ctypes.c_uint8]
_lib.lean_uor_r96_classify.restype = ctypes.c_uint8

def r96_classify(b):
    """Classify byte using R96 resonance classifier."""
    if not isinstance(b, int) or not 0 <= b <= 255:
        raise ValueError("Byte must be integer in range 0-255")
    return _lib.lean_uor_r96_classify(b)
```

### Node.js Integration

**N-API Approach:**
```cpp
// uor_addon.cc
#include <node_api.h>
#include "uor_ffi.h"

napi_value R96Classify(napi_env env, napi_callback_info info) {
    size_t argc = 1;
    napi_value args[1];
    napi_get_cb_info(env, info, &argc, args, nullptr, nullptr);
    
    uint32_t b;
    napi_get_value_uint32(env, args[0], &b);
    
    uint8_t result = lean_uor_r96_classify((uint8_t)b);
    
    napi_value napi_result;
    napi_create_uint32(env, result, &napi_result);
    return napi_result;
}
```

## Memory Management

### Ownership Model

The FFI follows a clear ownership model:

1. **Lean Runtime**: Owns all internal mathematical objects
2. **FFI Layer**: Provides borrowed references with defined lifetimes
3. **Language Bindings**: Responsible for converting and managing language types
4. **Applications**: Own their data and coordinate with bindings

### String Handling

For functions that might return strings in the future:

```c
// Caller owns the returned string, must free with lean_uor_free_string
char* lean_uor_get_version_string(void);
void lean_uor_free_string(char* str);
```

### Array Operations

For batch operations (future extension):

```c
// Process array of bytes, results written to output array
// Input and output arrays must have same length
int lean_uor_r96_classify_batch(
    const uint8_t* input, 
    uint8_t* output, 
    size_t length
);
```

## Error Handling Strategy

### C-Style Error Codes

The FFI uses consistent error codes:

```c
#define UOR_SUCCESS           0
#define UOR_ERROR_INVALID     1
#define UOR_ERROR_UNINITIALIZED 2
#define UOR_ERROR_MEMORY      3
#define UOR_ERROR_INTERNAL    4
```

### Language-Specific Translation

Each language binding translates C error codes to idiomatic error handling:

**Go:**
```go
func PhiEncode(page, byte uint8) (uint32, error) {
    result := C.lean_uor_phi_encode(C.uint8_t(page), C.uint8_t(byte))
    if result == 0 && (page >= 48 || byte >= 256) {
        return 0, fmt.Errorf("invalid coordinates: page=%d, byte=%d", page, byte)
    }
    return uint32(result), nil
}
```

**Rust:**
```rust
pub fn phi_encode(page: u8, byte: u8) -> Result<u32, UorError> {
    if page >= 48 {
        return Err(UorError::InvalidPage(page));
    }
    unsafe {
        Ok(lean_uor_phi_encode(page, byte))
    }
}
```

**Python:**
```python
def phi_encode(page, byte_val):
    if not (0 <= page < 48):
        raise ValueError(f"Page must be in range 0-47, got {page}")
    if not (0 <= byte_val < 256):
        raise ValueError(f"Byte must be in range 0-255, got {byte_val}")
    return _lib.lean_uor_phi_encode(page, byte_val)
```

## Cross-Language Compatibility

### ABI Versioning

The FFI includes version information to ensure compatibility:

```c
#define UOR_ABI_VERSION_MAJOR 1
#define UOR_ABI_VERSION_MINOR 0
#define UOR_ABI_VERSION_PATCH 0

uint32_t lean_uor_abi_version(void);
```

### Platform Considerations

**Calling Conventions:**
- Uses C calling convention (cdecl) for maximum compatibility
- No variadic functions to avoid platform differences
- Explicit sizing for all integer types

**Endianness:**
- All multi-byte values use host endianness
- No network byte order conversions needed

**Alignment:**
- Uses natural alignment for all types
- No packed structures in the interface

## Performance Considerations

### Hot Path Optimization

The most frequently used functions are optimized:

1. **Constants**: `lean_uor_pages()`, `lean_uor_bytes()`, etc. - should be cached
2. **R96 Classifier**: `lean_uor_r96_classify()` - can use lookup tables
3. **Φ Encoding**: Simple bit operations, minimal overhead

### Batch Operations

For high-throughput scenarios, batch operations reduce FFI overhead:

```c
// Future enhancement
int lean_uor_r96_classify_batch(
    const uint8_t* input,
    uint8_t* output,
    size_t count
);
```

### Zero-Copy Patterns

Where possible, the FFI avoids copying data:

```c
// Return constant references instead of copies
const uint8_t* lean_uor_get_r96_table(void); // Returns 256-element table
```

## Security Model

### Input Validation

Each FFI function validates its inputs:

```c
uint8_t lean_uor_r96_classify(uint8_t b) {
    // No validation needed - uint8_t is inherently valid
    return r96_classify_impl(b);
}

uint8_t lean_uor_phi_page(uint32_t code) {
    // Extract page and ensure it's in valid range
    uint8_t page = (code >> 8) & 0xFF;
    return page % 48; // Ensure valid page range
}
```

### Resource Limits

The FFI includes protection against resource exhaustion:

- Initialization can fail if system resources are insufficient
- Batch operations have maximum size limits
- Memory allocation failures are handled gracefully

## Future Extensions

### Planned Enhancements

1. **Async Operations**: Non-blocking versions of compute-intensive functions
2. **Streaming API**: Process data streams without buffering
3. **SIMD Optimization**: Vectorized operations for batch processing
4. **GPU Acceleration**: CUDA/OpenCL backends for parallel computation

### Backward Compatibility

The FFI is designed for evolution:

- Version negotiation allows feature detection
- Optional functions can be added without breaking existing code
- Deprecated functions remain available with warnings

## Debugging and Diagnostics

### Debug Mode

Build-time debug mode adds extensive checking:

```c
#ifdef UOR_DEBUG
#define UOR_ASSERT(cond) assert(cond)
#define UOR_LOG(msg) fprintf(stderr, "UOR: %s\n", msg)
#else
#define UOR_ASSERT(cond) 
#define UOR_LOG(msg)
#endif
```

### Performance Profiling

The FFI includes hooks for performance analysis:

```c
#ifdef UOR_PROFILE
extern void uor_profile_enter(const char* function);
extern void uor_profile_exit(const char* function);
#else
#define uor_profile_enter(f)
#define uor_profile_exit(f)
#endif
```

This FFI design provides a robust, flexible, and performant bridge between the verified mathematical core and practical applications across multiple programming languages.