# UOR FFI Implementation Guide

## Overview

This directory contains the Foreign Function Interface (FFI) for the UOR Prime Structure, allowing C and other languages to interact with the Lean implementation.

## Approaches for Using UOR FFI in C

### 1. Pure C Implementation (Recommended for Simplicity)

Use the header-only pure C implementation that requires no Lean runtime:

```c
#include "uor_ffi_hybrid.h"  // Don't define UOR_USE_LEAN_RUNTIME

int main() {
    uint32_t pages = UOR_PAGES();  // Returns 48
    uint8_t cls = UOR_R96_CLASSIFY(255);  // Returns 63
    return 0;
}
```

**Compile with:**
```bash
gcc -o myapp myapp.c
```

**Pros:**
- No dependencies
- Easy to compile and distribute
- Works on any platform
- Header-only implementation

**Cons:**
- Not verified by Lean's proof system
- Manual synchronization with Lean implementation

### 2. Lean Runtime Integration (For Verification)

Link against Lean's shared libraries for verified implementation:

```c
#define UOR_USE_LEAN_RUNTIME
#include "uor_ffi_hybrid.h"

int main() {
    UOR_INIT(0);  // Initialize Lean runtime
    uint32_t pages = UOR_PAGES();  // Calls Lean function
    UOR_FINALIZE();
    return 0;
}
```

**Compile with:**
```bash
gcc -o myapp myapp.c \
  -L.lake/build/lib/lean -Wl,-rpath,.lake/build/lib/lean \
  UOR_FFI_CAPI.so UOR_Atlas_Core.so UOR_Prime_Structure.so \
  -lInit_shared -lstdc++ -lgmp -lpthread -ldl -lm
```

**Pros:**
- Uses verified Lean implementation
- Guaranteed correctness
- Automatically updated with Lean changes

**Cons:**
- Complex dependencies (Lean runtime, libc++/libstdc++, libuv, gmp)
- Platform-specific builds
- Larger binary size

### 3. Static Library Bundle (For Distribution)

Create a self-contained static library:

```bash
./create_bundle.sh
gcc -o myapp myapp.c -L.lake/build/lib -lUOR_bundle -lstdc++ -lgmp -lpthread
```

**Pros:**
- Single library file
- No runtime dependencies
- Easier distribution

**Cons:**
- Still requires some system libraries (gmp, pthread)
- Larger binary size

## File Structure

```
ffi/
├── c/
│   ├── uor_ffi.h           # Original FFI header
│   ├── uor_ffi_hybrid.h    # Hybrid header (Lean or pure C)
│   ├── uor_init.c          # Lean runtime initialization
│   ├── minimal_wrapper.c   # Minimal C implementation
│   ├── test_ffi.c          # Full FFI test suite
│   ├── test_pure_c.c       # Pure C test (no Lean)
│   └── verify_ffi.c        # FFI verification tool
├── Makefile                # Build system
├── .clang-format          # Code formatting config
└── README.md              # This file
```

## Quick Start

### Pure C (Simplest)

```bash
# Compile and run pure C test
gcc -o test_pure ffi/c/test_pure_c.c
./test_pure
```

### With Lean Runtime

```bash
# Build Lean libraries
lake build UOR

# Try to build with Lean (may have dependency issues)
make -C ffi build

# Or use the hybrid approach
gcc -DUOR_USE_LEAN_RUNTIME -o test_lean ffi/c/test_pure_c.c \
  [lean libraries and dependencies]
```

## API Reference

All functions are available in both pure C and Lean-backed versions:

- `UOR_PAGES()` - Returns 48 (number of pages)
- `UOR_BYTES()` - Returns 256 (bytes per page)  
- `UOR_RCLASSES()` - Returns 96 (resonance classes)
- `UOR_R96_CLASSIFY(b)` - Classify byte to resonance class [0,95]
- `UOR_PHI_ENCODE(page, byte)` - Pack coordinates to 32-bit code
- `UOR_PHI_PAGE(code)` - Extract page from code
- `UOR_PHI_BYTE(code)` - Extract byte from code
- `UOR_TRUTH_ZERO(budget)` - Check if budget is zero (truth)
- `UOR_TRUTH_ADD(a, b)` - Check if sum is zero

## Testing

```bash
# Run pure C tests (always works)
gcc -o test_pure ffi/c/test_pure_c.c && ./test_pure

# Run full test suite (requires Lean)
make -C ffi test

# Run verification
make -C ffi verify
```

## Troubleshooting

### C++ Standard Library Conflicts

The Lean runtime is compiled with libc++ (LLVM) but most Linux systems use libstdc++ (GNU). This causes linking errors.

**Solutions:**
1. **Use Pure C Implementation** (Recommended)
   ```c
   // Don't define UOR_USE_LEAN_RUNTIME
   #include "uor_ffi_hybrid.h"
   ```

2. **Use Docker Container**
   ```bash
   docker build -f Dockerfile -t uor-ffi .
   docker run --rm -v $(pwd):/workspace uor-ffi make test-pure
   ```

3. **Match Toolchain**
   ```bash
   # Use clang with libc++
   CC=clang CXX=clang++ CXXFLAGS="-stdlib=libc++" make
   ```

### Symbol Not Found

If FFI symbols aren't exported from Lean:
1. Check that `@[export]` attribute is used in Lean code
2. Verify module is built with `precompileModules := true`
3. Use `nm -D` to check symbols in .so files

## Recommendations

1. **For Development:** Use pure C implementation (`uor_ffi_hybrid.h` without `UOR_USE_LEAN_RUNTIME`)
2. **For Testing:** Verify against both pure C and Lean implementations
3. **For Production:** Choose based on requirements:
   - Need verification guarantees? Use Lean runtime
   - Need simplicity/portability? Use pure C
   - Need both? Use hybrid header with compile-time switching