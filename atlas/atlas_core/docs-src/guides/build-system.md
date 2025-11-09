---
layout: default
title: Build System
sidebar: guides
---

# Build System Guide

The UOR Prime Structure FFI uses a hierarchical GNU Make build system that coordinates compilation across multiple languages and components. This guide explains the build system architecture, available targets, and configuration options.

## Build System Architecture

### Hierarchical Makefile Structure

```
/
├── Makefile           # Root coordinator
├── common.mk          # Shared variables and rules
├── lean/Makefile      # Lean library build
├── ffi/Makefile       # FFI layer build
├── pkg/               # Basic bindings
│   ├── go/Makefile
│   ├── python/Makefile
│   ├── rust/Makefile
│   └── node/Makefile
├── runtime/           # Enhanced bindings
│   ├── go/Makefile
│   ├── python/Makefile
│   ├── rust/Makefile
│   └── node/Makefile
└── tests/Makefile     # Test coordination
```

### Dependency Graph

```
lean (Lean 4 library)
│
├── ffi (C API layer)
│   │
│   ├── pkg/* (Basic bindings)
│   │   ├── go/
│   │   ├── python/
│   │   ├── rust/
│   │   └── node/
│   │
│   └── runtime/* (Enhanced bindings)
│       ├── go/
│       ├── python/
│       ├── rust/
│       └── node/
│
└── tests (Verification suite)
```

## Main Build Targets

### Primary Targets

#### `make all`
Builds the complete system in dependency order:
1. Lean library and CLI
2. FFI C API layer
3. All runtime language wrappers

```bash
make all
# Equivalent to:
# make lean
# make ffi  
# make runtime
```

#### `make lean`
Builds only the Lean components:
- Core mathematical library
- CLI verification tool
- Lean-to-C FFI exports

```bash
make lean
# Creates:
# - .lake/build/lib/libUOR.{a,so,dylib}
# - .lake/build/bin/uor-verify
```

#### `make ffi`
Builds the FFI layer (requires Lean):
- C API headers and libraries
- FFI test executables
- Packaging configuration files

```bash
make ffi
# Creates:
# - ffi/c/uor_ffi.h (header)
# - ffi tests and examples
```

#### `make runtime`
Builds all enhanced language runtime wrappers:

```bash
make runtime
# Builds:
# - runtime/go/uorffi/
# - runtime/python/uor_runtime/
# - runtime/rust/target/
# - runtime/node/build/
```

### Testing Targets

#### `make test`
Runs comprehensive test suite:
```bash
make test
# Runs tests for:
# - Lean verification
# - C FFI functionality
# - All language bindings
# - Integration tests
```

#### `make check`
Quick verification test:
```bash
make check
# Equivalent to:
# .lake/build/bin/uor-verify
```

### Maintenance Targets

#### `make clean`
Removes all build artifacts:
```bash
make clean
# Removes:
# - .lake/build/
# - All compiled binaries
# - Language-specific build artifacts
```

#### `make install`
Installs system-wide (requires sudo for default prefix):
```bash
sudo make install
# Installs to /usr/local/ by default
# Use: make PREFIX=/opt/uor install
```

#### `make format`
Formats source code (if tools available):
```bash
make format
# Formats:
# - Lean files with lean4-format
# - C files with clang-format
# - Go files with gofmt
# - Rust files with rustfmt
```

## Language-Specific Builds

### Go Bindings

#### Basic Package Bindings
```bash
make -C pkg/go all        # Build basic Go package
make -C pkg/go test       # Test basic bindings
make -C pkg/go install    # Install Go package
make -C pkg/go clean      # Clean Go artifacts
```

#### Enhanced Runtime
```bash
make -C runtime/go all    # Build enhanced Go runtime
make -C runtime/go test   # Test runtime features
make -C runtime/go bench  # Run Go benchmarks
```

### Python Bindings

#### Basic Package Bindings
```bash
make -C pkg/python all        # Build Python package
make -C pkg/python test       # Test Python bindings
make -C pkg/python install    # Install Python package
```

#### Enhanced Runtime
```bash
make -C runtime/python all    # Build Python runtime
make -C runtime/python test   # Test runtime
make -C runtime/python wheel  # Create distribution wheel
```

### Rust Bindings

#### Basic Package Bindings
```bash
make -C pkg/rust all          # Build Rust crate
make -C pkg/rust test         # Test Rust bindings
make -C pkg/rust doc          # Generate Rust docs
```

#### Enhanced Runtime
```bash
make -C runtime/rust all      # Build Rust runtime
make -C runtime/rust test     # Test runtime
make -C runtime/rust bench    # Run Rust benchmarks
```

### Node.js Bindings

#### Basic Package Bindings
```bash
make -C pkg/node all          # Build Node.js package
make -C pkg/node test         # Test Node.js bindings
make -C pkg/node install      # Install Node package
```

#### Enhanced Runtime
```bash
make -C runtime/node all      # Build Node.js runtime
make -C runtime/node test     # Test runtime
make -C runtime/node types    # Generate TypeScript types
```

## Configuration Options

### Build Variables

#### Build Type
```bash
make BUILD_TYPE=release      # Optimized build (default)
make BUILD_TYPE=debug        # Debug symbols and assertions
```

#### Verbosity
```bash
make VERBOSE=0               # Quiet output (default)
make VERBOSE=1               # Show all commands
```

#### Installation Prefix
```bash
make PREFIX=/opt/uor install      # Custom install location
make LIBDIR=/usr/lib64 install    # Custom library directory
```

#### Color Output
```bash
make NO_COLOR=1              # Disable colored output
```

### Environment Variables

#### Tool Selection
```bash
export CC=clang              # Use clang instead of gcc
export GO=go1.21.3           # Specific Go version
export CARGO=cargo           # Rust package manager
```

#### Lean Configuration
```bash
export LEAN_OPTS="--debug"   # Additional Lean options
```

#### Cross-Compilation
```bash
# Go cross-compilation
export GOOS=linux GOARCH=amd64
make -C runtime/go all

# Rust cross-compilation  
export CARGO_BUILD_TARGET=x86_64-unknown-linux-gnu
make -C runtime/rust all
```

## Build Process Details

### Phase 1: Lean Library Build

```bash
cd lean/
lake build                   # Build Lean library
lake build UOR              # Build specific modules
.lake/build/bin/uor-verify   # Test Lean implementation
```

**Outputs:**
- `.lake/build/lib/libUOR.a` - Static library
- `.lake/build/lib/libUOR.so` - Dynamic library (Linux)
- `.lake/build/lib/libUOR.dylib` - Dynamic library (macOS)
- `.lake/build/bin/uor-verify` - CLI verification tool

### Phase 2: FFI Layer Build

```bash
cd ffi/
make all                     # Build C examples and tests
gcc -I../c tests/test_ffi.c  # Compile FFI tests
```

**Outputs:**
- `ffi/c/uor_ffi.h` - C API header
- `ffi/examples/simple` - Example executable
- `ffi/examples/advanced` - Advanced example

### Phase 3: Language Bindings

Each language has specific build processes:

#### Go Build Process
```bash
cd runtime/go/
go mod tidy                  # Update dependencies
go build ./uorffi           # Build package
go test ./uorffi            # Run tests
```

#### Python Build Process
```bash
cd runtime/python/
python setup.py build       # Build extension
python setup.py test        # Run tests
python setup.py bdist_wheel # Create distribution
```

#### Rust Build Process
```bash
cd runtime/rust/
cargo build --release       # Build release version
cargo test                  # Run tests
cargo doc --open            # Generate and view docs
```

#### Node.js Build Process
```bash
cd runtime/node/
npm install                  # Install dependencies
npm run build               # Build native module
npm test                    # Run tests
```

## Advanced Build Options

### Parallel Builds

```bash
make -j$(nproc)             # Use all CPU cores
make -j4                    # Use 4 parallel jobs
```

### Selective Builds

```bash
# Build only specific components
make lean                   # Lean only
make -C runtime/go          # Go runtime only
make -C pkg/python          # Python basic only

# Build multiple specific targets
make lean ffi               # Lean and FFI, skip runtime
```

### Build Profiles

#### Development Profile
```bash
make BUILD_TYPE=debug VERBOSE=1
# - Debug symbols
# - Verbose output
# - Additional assertions
# - Faster compilation
```

#### Release Profile
```bash
make BUILD_TYPE=release
# - Optimized code
# - No debug symbols
# - Production-ready
```

#### CI/CD Profile
```bash
make BUILD_TYPE=release NO_COLOR=1 VERBOSE=1
# - Optimized build
# - No color for logs
# - Verbose for debugging
```

## Troubleshooting Build Issues

### Common Problems

#### Lean Build Failures
```bash
# Clear cache and rebuild
lake clean
make clean
make lean

# Update Lean toolchain
elan self update
elan install stable
```

#### CGO Build Errors
```bash
# Verify CGO is enabled
go env CGO_ENABLED

# Set compiler explicitly
export CC=gcc
make -C runtime/go clean all
```

#### Missing Dependencies
```bash
# Check for required tools
make check-deps  # If available
which lake go rust node npm
```

#### Permission Issues
```bash
# Install to user directory
make PREFIX=$HOME/.local install

# Or fix permissions
sudo make install
```

### Build Environment Debugging

#### Check Variables
```bash
make help                   # Show current configuration
make -C runtime/go help     # Language-specific help
```

#### Verbose Output
```bash
make VERBOSE=1 all         # See all commands
make VERBOSE=1 -C lean     # Debug specific component
```

#### Environment Verification
```bash
# Verify tools are available
which lake cc go cargo npm rustc node

# Check versions
lake --version
go version
cargo --version
```

## Integration with IDEs

### VS Code
```json
// .vscode/tasks.json
{
    "version": "2.0.0",
    "tasks": [
        {
            "label": "Build All",
            "type": "shell",
            "command": "make",
            "args": ["all"],
            "group": "build",
            "presentation": {"echo": true, "reveal": "always"}
        },
        {
            "label": "Quick Check",
            "type": "shell", 
            "command": "make",
            "args": ["check"],
            "group": "test"
        }
    ]
}
```

### CLion/IntelliJ
Set up external tools for common make targets.

### Emacs
Use `M-x compile` with make commands.

## Custom Build Extensions

### Adding New Languages

1. Create `runtime/newlang/Makefile`:
```makefile
include ../../common.mk

all: build

build:
	# Language-specific build commands

test:
	# Language-specific tests

install:
	# Installation commands

clean:
	# Cleanup
```

2. Update root Makefile:
```makefile
SUBDIRS := lean ffi runtime tests pkg newlang
```

### Custom Build Targets

Add to language-specific Makefiles:
```makefile
benchmark:
	# Performance benchmarks

docs:
	# Generate documentation

package:
	# Create distribution packages
```

This build system provides a robust, scalable foundation for managing the complex multi-language UOR Prime Structure FFI project while maintaining consistency and ease of use.