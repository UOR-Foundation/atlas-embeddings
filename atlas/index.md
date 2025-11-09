# UOR Prime Structure FFI Documentation

## Overview

The **UOR Prime Structure** is a mathematical framework implementing a 12,288-element holographic structure through the **Φ-Atlas-12288** system. This documentation covers the Foreign Function Interface (FFI) and language bindings for interacting with the formally verified Lean 4 implementation.

## Key Concepts

### Prime Structure (48×256)
- **48 Pages**: Periodic organization of the structure
- **256 Bytes per Page**: Each page contains 256 byte-addressable elements
- **12,288 Total Elements**: Complete boundary structure (48 × 256)

### R96 Resonance Classification
- **96 Resonance Classes**: Compression from 256 byte values to 96 equivalence classes
- **3/8 Compression Ratio**: Efficient representation maintaining essential properties
- **Periodic Mapping**: Systematic classification preserving structure

### Holographic Principle
- **Bulk↔Boundary Correspondence**: Information equivalence between dimensions
- **Master Isomorphism Φ**: Formal correspondence preserving structure
- **Conservation Laws**: Truth defined as conservation at budget zero

## Quick Start

### Installation

Choose your preferred language binding:

```bash
# Go
cd pkg/go && go get

# Python
pip install pkg/python/

# Rust
cd pkg/rust && cargo build

# Node.js
cd pkg/node && npm install
```

### Basic Usage

```c
// C - Using minimal wrapper
#include "uor_ffi_hybrid.h"

int main() {
    uint32_t pages = UOR_PAGES();        // 48
    uint8_t cls = UOR_R96_CLASSIFY(255); // 63
    uint32_t code = UOR_PHI_ENCODE(3, 16);
    return 0;
}
```

## Architecture

The repository provides three layers of abstraction:

1. **Core Implementation** (`lean/`) - Formally verified Lean 4 mathematics
2. **FFI Layer** (`ffi/`) - C interface with minimal wrapper
3. **Language Bindings** - Two tiers of bindings:
   - **Basic** (`pkg/`) - Direct function access
   - **Enhanced** (`runtime/`) - Rich object-oriented APIs

## Documentation Sections

- [**API Reference**](api/) - Complete API documentation for all bindings
- [**Architecture Guide**](guides/architecture) - Technical implementation details and system design
- [**Mathematical Background**](guides/mathematics) - Theoretical foundations and formal verification
- [**Getting Started**](guides/getting-started) - Quick start guide and first examples
- [**Build System**](guides/build-system) - Understanding the Makefile hierarchy

## Repository Structure

```
atlas-12288/
├── lean/           # Lean 4 formal verification
├── ffi/            # C FFI layer
├── pkg/            # Basic language bindings
├── runtime/        # Enhanced language bindings
├── tests/          # Test suites
└── docs/           # Generated documentation
```

## Key Features

- **Formal Verification**: Core mathematics proven in Lean 4
- **Cross-Language Support**: Go, Python, Rust, Node.js bindings
- **Minimal Dependencies**: Pure C implementation available
- **Comprehensive Testing**: Full test coverage across all bindings
- **CI/CD Integration**: Automated testing and documentation

## Contributing

See [CONTRIBUTING.md](https://github.com/afflom/atlas-12288/blob/main/CONTRIBUTING.md) for guidelines.

## License

This project is open source. See [LICENSE](https://github.com/afflom/atlas-12288/blob/main/LICENSE) for details.

---

*Generated with the UOR Prime Structure FFI build system*