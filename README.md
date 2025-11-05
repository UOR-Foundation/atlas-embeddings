# UOR Prime Structure FFI

A Lean 4 implementation of the Prime Structure/Φ-Atlas-12288 mathematical framework with FFI bindings for multiple languages.

## Overview

This project implements the core mathematical concepts from the Universal Object Reference (UOR) Prime Structure specification, providing:

- **12,288-element structure** (48×256) representing the fundamental mathematical object
- **R96 resonance classifier** mapping 256 byte values to 96 resonance classes (3/8 compression)
- **Φ boundary encoding** for page/byte coordinate packing
- **Truth ≙ conservation** budget semantics
- **Multi-language FFI** supporting Go, Rust, Node.js, and C

## Mathematical Background

The Prime Structure is built on several key mathematical principles:

- **Unity Constraint**: α₄α₅ = 1 creating fundamental symmetries
- **96 Resonance Classes**: Exactly 96 distinct values from 8-bit patterns
- **Conservation Laws**: Triple-cycle invariant with sum 687.110133...
- **Holographic Duality**: Bulk↔boundary correspondence via master isomorphism Φ

For detailed mathematical context, see the formal Lean implementation in the `/lean/` directory.

## Repository Structure

```
/
├─ README.md                         # This file
├─ lean-toolchain                     # Lean version specification
├─ lakefile.lean                      # Build configuration
├─ lean/
│  └─ UOR/
│     ├─ Prime/
│     │  └─ Structure.lean           # 48×256 boundary + R96 (core math)
│     ├─ Atlas/
│     │  └─ Core.lean                # Φ-Atlas-12288 record instance
│     ├─ FFI/
│     │  └─ CAPI.lean                # Exported C ABI
│     └─ Verify/
│        └─ CLI.lean                 # CLI for testing
├─ ffi/
│  └─ c/
│     ├─ uor_ffi.h                   # C header: stable ABI
│     ├─ minimal_wrapper.c           # Minimal C implementation
│     └─ uor_init.c                  # Lean runtime initialization
├─ pkg/
│  ├─ go/                            # Go bindings (basic)
│  ├─ python/                        # Python bindings
│  ├─ rust/                          # Rust bindings (basic)
│  └─ node/                          # Node.js bindings
├─ runtime/
│  ├─ go/                            # Enhanced Go wrapper
│  ├─ rust/                          # Enhanced Rust wrapper
│  └─ node/                          # Enhanced Node.js wrapper
└─ tests/
   └─ c/test_ffi.c                   # C smoke test
```

## Building

### Prerequisites

- Lean 4 (stable release)
- C compiler (gcc/clang)
- GNU Make
- Optional: Go, Rust, Node.js for language-specific wrappers

### Quick Start with Make

The project includes a hierarchical Makefile system for easy building:

```bash
# Build everything (Lean library, FFI, and runtime wrappers)
make all

# Run all tests
make test

# Quick verification check
make check

# Install to system (requires sudo for default prefix)
sudo make install

# Clean all build artifacts
make clean
```

### Make Targets

#### Main Targets
- `make all` - Build everything (lean, ffi, runtime)
- `make lean` - Build Lean library only
- `make ffi` - Build FFI components
- `make runtime` - Build all language wrappers
- `make test` - Run all tests
- `make check` - Quick verification test
- `make clean` - Remove all build artifacts
- `make install` - Install libraries and headers
- `make format` - Format source code (if formatters available)
- `make docs` - Build comprehensive documentation

#### Subdirectory Targets
```bash
# Build specific components
make -C lean all        # Build Lean library and executable
make -C ffi all         # Build FFI layer and tests
make -C pkg all         # Build all language bindings (basic)
make -C runtime all     # Build enhanced language wrappers
make -C tests all       # Run all tests

# Run specific tests
make -C tests test-lean        # Lean verification only
make -C tests test-c           # C tests only
make -C tests test-pkg         # Package binding tests
make -C tests test-runtime     # Enhanced wrapper tests
make -C tests benchmark        # Performance benchmarks
```

#### Configuration Variables
```bash
# Build with custom settings
make BUILD_TYPE=debug          # Debug build
make VERBOSE=1                 # Verbose output
make PREFIX=/opt/uor install   # Custom install prefix
make NO_COLOR=1                # Disable colored output
```

## Documentation

The project includes comprehensive documentation that can be built using the make system:

```bash
# Build all documentation
make docs

# Build specific documentation types
make -C docs html      # HTML documentation with navigation
make -C docs api       # API reference from Lean sources  
make -C docs capi      # C API documentation from headers
make -C docs langdocs  # Language wrapper documentation
make -C docs markdown  # Collect and process markdown files
make -C docs pdf       # PDF documentation (requires pandoc)

# Serve documentation locally
make -C docs serve     # Starts HTTP server at localhost:8000
```

### Documentation Structure

After building, documentation is available in `docs/build/`:

- `html/index.html` - Main documentation site with navigation
- `api/` - Lean API documentation and module reference
- `capi/` - C API function signatures and constants
- `lang/` - Go, Rust, and Node.js wrapper documentation
- `markdown/` - Processed documentation files

The HTML documentation provides a comprehensive view of:
- **Getting Started**: README, API reference, C API reference  
- **Language Bindings**: Go, Rust, Node.js wrapper documentation
- **Additional Resources**: Documentation index and Lean language links

### Manual Build Steps (without Make)

1. **Build Lean library and CLI**:
```bash
lake build
```

Artifacts will be generated under `.lake/build/lib/` (libUOR.{a,so,dylib})

2. **Build and run CLI verification**:
```bash
.lake/build/bin/uor-verify
echo $?  # Should output 0 for success
```

3. **Build C smoke test**:
```bash
cc -Iffi/c -L.lake/build/lib tests/c/test_ffi.c -o tests/c/test_ffi \
   -lUOR -lLean -lpthread -ldl
./tests/c/test_ffi  # Should output "OK"
```

## API Reference

### Constants

- `lean_uor_pages()` → 48 (number of pages)
- `lean_uor_bytes()` → 256 (bytes per page)
- `lean_uor_rclasses()` → 96 (resonance classes)
- `lean_uor_abi_version()` → 1 (ABI version)

### R96 Classifier

- `lean_uor_r96_classify(b)` → [0,95]
  - Returns the resonance class for byte `b`

### Φ Boundary Encoding

- `lean_uor_phi_encode(page, byte)` → 32-bit code
  - Packs (page, byte) as `(page << 8) | byte`
- `lean_uor_phi_page(code)` → page (mod 48)
  - Extracts page component
- `lean_uor_phi_byte(code)` → byte
  - Extracts byte component (low 8 bits)

### Truth ≙ Conservation

- `lean_uor_truth_zero(budget)` → 0/1
  - Returns 1 if budget equals 0 (truth)
- `lean_uor_truth_add(a, b)` → 0/1
  - Returns 1 if `a + b == 0` (additive conservation)

## Language Bindings

The repository provides two tiers of language bindings:

### Basic Bindings (`pkg/`)
Minimal wrappers providing direct access to core functions:

**Go** (`pkg/go/`)
```go
import uor "github.com/your-repo/pkg/go/src"
fmt.Println("Pages:", uor.Pages())      // 48
fmt.Println("R96(255):", uor.R96(255))  // Class [0,95]
```

**Python** (`pkg/python/`)  
```python
import uor
print(f"Pages: {uor.pages()}")         # 48
print(f"R96(255): {uor.r96(255)}")     # Class [0,95]
```

**Rust** (`pkg/rust/`)
```rust
use uor_ffi;
println!("Pages: {}", uor_ffi::pages()); // 48
```

**Node.js** (`pkg/node/`)
```javascript
const uor = require('uor-ffi');
console.log('Pages:', uor.pages());     // 48
```

### Enhanced Bindings (`runtime/`)
Rich object-oriented APIs with comprehensive types:

**Go** (`runtime/go/`)
```go
import "path/to/runtime/go/uorffi"
coord := uorffi.NewPhiCoordinate(3, 16)
fmt.Println("Encoded:", coord.Code())
```

**Rust** (`runtime/rust/`)
```rust
use uor_runtime::*;
let coord = PhiCoordinate::new(3, 16)?;
println!("Page: {}", coord.page());
```

**Node.js** (`runtime/node/`)
```javascript
const { PhiCoordinate } = require('./runtime/node');
const coord = new PhiCoordinate(3, 16);
console.log('Code:', coord.code);
```

## Mathematical Significance

The FFI exposes key invariants from the Prime Structure formalization:

1. **R96 Compression**: The 96/256 = 3/8 ratio is a universal compression bound
2. **Page Structure**: 48-periodic organization emerges from unity constraint
3. **Conservation Laws**: Truth ≙ conservation at budget 0
4. **Holographic Principle**: Boundary encodes bulk information

## Testing

Run the verification suite:
```bash
# All tests
make test

# Component-specific tests
make -C lean test               # Lean verification
make -C ffi test               # C FFI tests  
make -C pkg test               # Basic bindings
make -C runtime test           # Enhanced bindings

# Language-specific tests
make -C pkg test-go            # Go basic bindings
make -C pkg test-python        # Python bindings
make -C runtime test-rust      # Rust enhanced bindings
make -C runtime test-node      # Node.js enhanced bindings
```

## Contributing

Contributions should maintain the mathematical integrity of the Prime Structure invariants. Key requirements:

- Preserve R96 count (exactly 96 resonance classes)
- Maintain unity constraint α₄α₅ = 1
- Ensure conservation laws hold
- Document any new mathematical insights

## License

This implementation provides formal verification of the mathematical framework through Lean 4. See individual files for specific licensing information.

## References

- Lean 4 Implementation (lean/UOR/)
- Prime Structure Module (lean/UOR/Prime/Structure.lean)
- Atlas Core Module (lean/UOR/Atlas/Core.lean)
- FFI C API (lean/UOR/FFI/CAPI.lean)