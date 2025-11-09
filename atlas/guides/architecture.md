---
layout: default
title: System Architecture
sidebar: guides
---

# System Architecture

The UOR Prime Structure FFI is designed as a multi-layered system that provides mathematically verified functionality through multiple programming languages while maintaining consistency and performance.

## High-Level Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                        Applications                             │
│    ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐         │
│    │   Go    │  │  Rust   │  │ Node.js │  │ Python  │   ...   │
│    │   App   │  │   App   │  │   App   │  │   App   │         │
│    └─────────┘  └─────────┘  └─────────┘  └─────────┘         │
└─────────────────────────────────────────────────────────────────┘
            │           │           │           │
            ▼           ▼           ▼           ▼
┌─────────────────────────────────────────────────────────────────┐
│                 Language Bindings Layer                        │
│  ┌───────────┐ ┌───────────┐ ┌───────────┐ ┌───────────┐      │
│  │ Go Wrapper│ │Rust Wrapper││Node Wrapper││Py Wrapper │      │
│  │           │ │           │ │           │ │           │      │
│  │ pkg/   ←──┼─│ pkg/   ←──┼─│ pkg/   ←──┼─│ pkg/      │      │
│  │ runtime/  │ │ runtime/  │ │ runtime/  │ │ runtime/  │      │
│  └───────────┘ └───────────┘ └───────────┘ └───────────┘      │
└─────────────────────────────────────────────────────────────────┘
            │           │           │           │
            ▼           ▼           ▼           ▼
┌─────────────────────────────────────────────────────────────────┐
│                      FFI Interface Layer                       │
│                         (ffi/)                                 │
│                                                                 │
│  ┌─────────────────────────────────────────────────────────┐  │
│  │            C ABI Definition (uor_ffi.h)                 │  │
│  │                                                         │  │
│  │  • Function signatures                                  │  │
│  │  • Data type definitions                                │  │
│  │  • Memory management contracts                          │  │
│  │  • Cross-language calling conventions                   │  │
│  └─────────────────────────────────────────────────────────┘  │
│                                                                 │
│  ┌─────────────────────────────────────────────────────────┐  │
│  │         Initialization Layer (uor_init.c)               │  │
│  │                                                         │  │
│  │  • Lean runtime initialization                          │  │
│  │  • Resource management                                  │  │
│  │  • Error handling setup                                 │  │
│  └─────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
            │           │           │           │
            ▼           ▼           ▼           ▼
┌─────────────────────────────────────────────────────────────────┐
│                   Mathematical Core                             │
│                       (lean/)                                   │
│                                                                 │
│  ┌─────────────────────────────────────────────────────────┐  │
│  │                Lean Implementation                       │  │
│  │              (Verified Mathematics)                      │  │
│  │                                                         │  │
│  │  UOR/                                                   │  │
│  │  ├─ Prime/Structure.lean    # 48×256 + R96 core math   │  │
│  │  ├─ Atlas/Core.lean         # Φ-Atlas-12288 instance   │  │
│  │  ├─ FFI/CAPI.lean           # C ABI exports            │  │
│  │  └─ Verify/CLI.lean         # Testing framework        │  │
│  └─────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
```

## Layer Descriptions

### 1. Mathematical Core (Lean Layer)

The foundation is built on formally verified mathematics implemented in Lean 4:

**Key Components:**
- **Prime/Structure.lean**: Core 48×256 boundary structure and R96 resonance classifier
- **Atlas/Core.lean**: Φ-Atlas-12288 record instance with holographic properties
- **FFI/CAPI.lean**: Exported C ABI functions with Lean verification
- **Verify/CLI.lean**: Command-line verification tools

**Mathematical Properties:**
- **Unity Constraint**: α₄α₅ = 1 creating fundamental symmetries
- **R96 Resonance Classes**: Exactly 96 distinct classes from 256 byte values
- **Conservation Laws**: Triple-cycle invariant with sum 687.110133...
- **Holographic Duality**: Bulk↔boundary correspondence via isomorphism Φ

### 2. FFI Interface Layer

The FFI layer acts as an intermediary protocol specification:

**Purpose:**
- Defines stable C ABI for cross-language compatibility
- Handles Lean runtime initialization and cleanup
- Provides memory management contracts
- Ensures consistent behavior across all language bindings

**Files:**
- `ffi/c/uor_ffi.h` - C header with function signatures
- `ffi/c/uor_init.c` - Runtime initialization
- `ffi/c/minimal_wrapper.c` - Minimal C implementation option

**Runtime Options:**
- **Lean Runtime**: Uses verified Lean implementation via dynamic linking
- **Pure Implementation**: Language-native implementations without FFI overhead
- **Hybrid**: Runtime selection between Lean and pure implementations

### 3. Language Bindings Layer

Two-tier approach for different use cases:

#### Basic Bindings (pkg/)
Minimal wrappers for direct FFI access:
- Direct mapping to C ABI functions
- Minimal overhead and memory footprint
- Suitable for performance-critical applications
- Simple integration

#### Enhanced Runtime (runtime/)
Rich object-oriented APIs:
- Type-safe interfaces with comprehensive error handling
- Object-oriented design patterns
- Advanced features like batch operations
- Idiomatic language conventions

### 4. Application Layer

User applications built on top of the language bindings:
- Domain-specific logic
- Integration with other systems
- User interfaces and APIs
- Performance optimizations

## Component Interactions

### Data Flow

```
Application Request
        │
        ▼
Language Wrapper (Type Conversion)
        │
        ▼
FFI Interface (C ABI)
        │
        ▼ (if using Lean runtime)
Lean Mathematical Core (Verified Computation)
        │
        ▼
Result (propagated back up)
```

### Memory Management

Each layer has specific responsibilities:

**Lean Layer:**
- Manages internal mathematical objects
- Handles garbage collection for Lean runtime
- Provides memory-safe operations

**FFI Layer:**
- Defines ownership contracts
- Handles string and array allocation/deallocation
- Provides error codes for memory issues

**Language Bindings:**
- Convert between language types and C types
- Integrate with language-specific garbage collectors
- Handle resource cleanup (RAII, finalizers, etc.)

### Error Handling

Errors are propagated through consistent patterns:

1. **Lean Level**: Mathematical assertions and proofs prevent many error classes
2. **FFI Level**: C-style error codes (0 = success, non-zero = error)
3. **Language Level**: Idiomatic error handling (exceptions, Result types, etc.)

## Design Decisions

### Why Multi-Layered Architecture?

1. **Separation of Concerns**: Mathematical logic separate from language-specific details
2. **Verification**: Lean layer provides formal proofs of correctness
3. **Performance Options**: Choice between verified and optimized implementations
4. **Language Neutrality**: FFI provides common interface across languages
5. **Maintainability**: Changes to math don't require updating all language bindings

### Why Two Binding Tiers?

**Basic Bindings (pkg/):**
- Minimal dependencies
- Low overhead for simple use cases
- Easy to understand and debug
- Direct access to all FFI functions

**Enhanced Runtime (runtime/):**
- Better developer experience
- Type safety and error handling
- Object-oriented patterns familiar to developers
- Advanced features like coordinate objects

### Pure vs. Lean Runtime

**Lean Runtime Advantages:**
- Mathematically verified correctness
- Consistent behavior across all languages
- Access to advanced Lean-specific features
- Single source of truth for algorithms

**Pure Implementation Advantages:**
- No external dependencies
- Better performance for simple operations
- Easier deployment and distribution
- Integration with language-specific optimizations

## Compilation and Linking

### Static Linking Model
```
┌─────────────────┐    ┌─────────────────┐
│ Language App    │    │ Language App    │
├─────────────────┤    ├─────────────────┤
│ Language Wrapper│    │ Language Wrapper│
├─────────────────┤    ├─────────────────┤
│ Pure Impl       │    │ FFI Interface   │
└─────────────────┘    ├─────────────────┤
                       │ Lean Library    │
                       └─────────────────┘
   No Dependencies         With Lean
```

### Build System Integration

The Makefile hierarchy reflects the architecture:
- Root Makefile coordinates all layers
- `lean/Makefile` builds verified core
- `ffi/Makefile` builds interface layer
- `pkg/*/Makefile` builds basic bindings
- `runtime/*/Makefile` builds enhanced bindings

## Performance Characteristics

### Layer Overhead

1. **Application → Language Wrapper**: Minimal (function call)
2. **Language Wrapper → FFI**: Low (type conversion)
3. **FFI → Lean**: Moderate (cross-language call)
4. **Lean Computation**: Variable (depends on operation)

### Optimization Strategies

- **Pure Implementations**: Eliminate FFI overhead
- **Batch Operations**: Reduce cross-layer calls
- **Caching**: Store frequently accessed constants
- **SIMD**: Use language-specific optimizations

## Security Model

### Trust Boundaries

1. **Lean Mathematical Core**: Highest trust (formally verified)
2. **FFI Interface**: Moderate trust (C ABI safety)
3. **Language Bindings**: Language-specific trust model
4. **Applications**: User-defined security model

### Safety Guarantees

- **Mathematical Correctness**: Proven by Lean verification
- **Memory Safety**: Protected by language-specific features
- **Type Safety**: Enforced by static typing where available
- **ABI Stability**: Versioned interface prevents incompatibilities

## Extensibility

### Adding New Languages

1. Create binding directory under `pkg/` or `runtime/`
2. Implement FFI interface using language's C interop
3. Add type conversions and error handling
4. Create idiomatic API wrapper
5. Add tests and documentation

### Adding New Functions

1. Define mathematics in Lean
2. Export via FFI/CAPI.lean
3. Update C header (uor_ffi.h)
4. Update all language bindings
5. Add comprehensive tests

This architecture ensures that mathematical correctness is preserved while providing flexible, performant interfaces for diverse use cases across multiple programming languages.