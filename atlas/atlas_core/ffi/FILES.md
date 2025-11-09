# FFI Directory Structure

## Core Files

### Headers (`c/`)
- `uor_ffi.h` - Main FFI C API definitions
- `uor_ffi_hybrid.h` - Hybrid header supporting both Lean and pure C backends
- `uor_init.c` - Lean runtime initialization
- `minimal_wrapper.c` - Pure C implementation of all functions

### Tests (`c/`)
- `test_pure_c.c` - Pure C implementation tests
- `test_ffi.c` - Comprehensive FFI test suite
- `verify_ffi.c` - Verification tool with multiple levels

### Examples (`examples/`)
- `simple.c` - Basic API usage demonstration
- `advanced.c` - Performance testing and validation
- `Makefile` - Build system for examples

### Documentation
- `README.md` - Main usage guide and API reference
- `ARCHITECTURE.md` - System design and implementation strategy
- `FILES.md` - This file

### Build System
- `Makefile` - Complete build system with test, verify, and install targets
- `.clang-format` - Code formatting configuration
- `Dockerfile` - Container for consistent build environment

## Usage

### Quick Start
```bash
# Test pure C implementation
make test-pure

# Build and run examples
cd examples && make run

# Run all tests
make test
```

### Essential Make Targets
- `make clean` - Remove build artifacts
- `make test-pure` - Test pure C implementation (no dependencies)
- `make headers` - Verify headers are present
- `make pkg-config` - Generate pkg-config file