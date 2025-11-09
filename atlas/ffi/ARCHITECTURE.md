# FFI Architecture

## Overview

The FFI layer is an **intermediary representation** that bridges Lean with multiple target languages.

```
┌─────────────────────────────────────────────┐
│            Lean Implementation              │
│         (Verified Mathematics)              │
└─────────────────┬───────────────────────────┘
                  │
                  ▼
┌─────────────────────────────────────────────┐
│         FFI Interface Layer                 │
│        (@ffi/ - This Directory)             │
│                                             │
│  • C ABI Definition (uor_ffi.h)            │
│  • Initialization (uor_init.c)             │
│  • Symbol Exports from Lean                │
└─────────────┬───────────────────────────────┘
              │
              ├────────────┬────────────┬────────────┐
              ▼            ▼            ▼            ▼
        ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐
        │    Go    │ │   Rust   │ │  Node.js │ │  Python  │
        │ Wrapper  │ │ Wrapper  │ │ Wrapper  │ │ Wrapper  │
        └──────────┘ └──────────┘ └──────────┘ └──────────┘
              │            │            │            │
              ▼            ▼            ▼            ▼
        ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐
        │    Go    │ │   Rust   │ │   Node   │ │  Python  │
        │   App    │ │   App    │ │   App    │ │   App    │
        └──────────┘ └──────────┘ └──────────┘ └──────────┘
```

## The FFI Contract

The FFI layer defines:

1. **Function Signatures** - What functions are available
2. **Data Types** - How data is represented (uint8_t, uint32_t, etc.)
3. **Calling Convention** - C ABI for cross-language compatibility
4. **Memory Management** - Who allocates/frees memory

## Runtime Choices

Each language wrapper can choose its runtime:

### Option 1: Lean Runtime (Dynamic Linking)
```
Go App → Go Wrapper → C FFI → Lean .so → Lean Runtime
```

**Go Example:**
```go
// runtime/go/uorffi/uorffi.go
package uorffi

// #cgo LDFLAGS: -L${SRCDIR}/../../../.lake/build/lib/lean -lUOR_FFI_CAPI
// #include "uor_ffi.h"
import "C"

func Pages() uint32 {
    return uint32(C.lean_uor_pages())  // Calls Lean implementation
}
```

### Option 2: Pure Implementation (No Lean)
```
Go App → Go Wrapper → Pure Go Implementation
```

**Go Example:**
```go
// runtime/go/uorffi/uorffi_pure.go
package uorffi

func Pages() uint32 {
    return 48  // Pure Go, no FFI needed
}
```

### Option 3: Hybrid (Runtime Selection)
```
Go App → Go Wrapper → [Choose at runtime]
                       ├→ C FFI → Lean
                       └→ Pure Go
```

**Go Example:**
```go
// runtime/go/uorffi/uorffi_hybrid.go
package uorffi

var useLeanRuntime = os.Getenv("UOR_USE_LEAN") == "1"

func Pages() uint32 {
    if useLeanRuntime {
        return uint32(C.lean_uor_pages())  // Lean
    }
    return 48  // Pure Go
}
```

## Language-Specific Wrappers

Each language wrapper handles:

1. **Type Conversion** - Language types ↔ C types
2. **Memory Management** - GC integration
3. **Error Handling** - Language idioms
4. **Runtime Choice** - Lean vs Pure

### Go Wrapper (`runtime/go/`)
- Uses CGO for FFI
- Can compile with or without CGO
- `go build -tags lean` for Lean runtime
- `go build` for pure Go

### Rust Wrapper (`runtime/rust/`)
- Uses `bindgen` for FFI
- Feature flags for runtime choice
- `cargo build --features lean-runtime`
- `cargo build` for pure Rust

### Node.js Wrapper (`runtime/node/`)
- Uses `node-ffi-napi` or N-API
- Can use WASM for browser
- `npm run build:lean` for Lean
- `npm run build:pure` for pure JS

### Python Wrapper (`runtime/python/`)
- Uses `ctypes` or `cffi`
- Conda package for Lean deps
- `pip install uor[lean]` for Lean
- `pip install uor` for pure Python

## The Intermediary Role

The FFI (`@ffi/`) is intermediary because:

1. **It doesn't implement the logic** - That's in Lean or pure implementations
2. **It doesn't handle language specifics** - That's in wrappers
3. **It defines the interface** - The contract all implementations follow

Think of it like a **protocol specification**:
- HTTP doesn't implement web servers
- But all web servers speak HTTP
- FFI doesn't implement the math
- But all wrappers speak the FFI protocol

## Compilation Flow

```bash
# Step 1: Build Lean → FFI symbols
lake build UOR
# Creates: .lake/build/lib/lean/*.so with exported symbols

# Step 2: Each language compiles against FFI
cd runtime/go && go build     # Go reads uor_ffi.h
cd runtime/rust && cargo build # Rust reads uor_ffi.h
cd runtime/node && npm build   # Node reads uor_ffi.h

# Step 3: Runtime linking (if using Lean)
# Each app links against Lean .so files at runtime
# OR uses pure implementation compiled into the wrapper
```

## Summary

- **FFI is the interface specification**, not the implementation
- **Wrappers are language-specific** bindings to that interface
- **Runtime can be Lean or pure**, chosen by the wrapper
- **"Works everywhere"** means the interface is portable, not that one binary runs everywhere

The FFI ensures all languages can interoperate with the same mathematical constants and operations, whether backed by Lean's verified implementation or pure reimplementations in each language.