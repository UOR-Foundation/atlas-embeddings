# Atlas Bridge v0.5 - Build Instructions

## Quick Start

### Option 1: Verification Script (Recommended)

The easiest way to build, test, and verify Atlas Bridge:

```bash
bash tools/verify_bridge.sh
```

This script:
- Detects BLAS availability
- Builds the library with optimal flags
- Compiles and runs all unit tests
- Generates certificate with metrics verification
- Enforces quality thresholds

### Option 2: Makefile

Build the library using the Makefile:

```bash
cd atlas
make              # Build with auto-detected BLAS
make USE_BLAS=no  # Build without BLAS
make USE_BLAS=yes # Force BLAS (fails if not found)
make static       # Build static library
make install      # Install to /usr/local (requires sudo)
```

### Option 3: CMake

Cross-platform build using CMake:

```bash
mkdir build
cd build
cmake ..
make
make test  # Run tests via CTest
```

## Detailed Build Instructions

### Prerequisites

**Required:**
- C compiler (gcc, clang) with C11 support
- Make or CMake
- Standard math library (libm)

**Optional (for better performance):**
- OpenBLAS or CBLAS (for BLAS acceleration)
- AVX2-capable CPU (for SIMD acceleration)

### Installing Dependencies

#### Ubuntu/Debian
```bash
sudo apt-get update
sudo apt-get install build-essential cmake
sudo apt-get install libopenblas-dev  # Optional: BLAS support
```

#### macOS
```bash
brew install gcc cmake
brew install openblas  # Optional: BLAS support
```

#### Other Linux
```bash
# Install your distro's build tools and optionally:
# - openblas-devel (Fedora/RHEL)
# - libopenblas-dev (Debian/Ubuntu)
```

### Build Configurations

#### Debug Build
```bash
cd atlas
make clean
CFLAGS="-g -O0" make
```

#### Release Build
```bash
cd atlas
make clean
make  # Default is optimized (-O2)
```

#### With BLAS Acceleration
```bash
cd atlas
make USE_BLAS=auto  # Auto-detect (default)
# OR
cmake -DUSE_BLAS=ON ..
```

#### Without BLAS (Portable)
```bash
cd atlas
make USE_BLAS=no
# OR
cmake -DUSE_BLAS=OFF ..
```

#### Static Library
```bash
cd atlas
make static
```

### CMake Configuration Options

```bash
cmake [OPTIONS] ..

Options:
  -DUSE_BLAS=ON/OFF          Enable BLAS acceleration (default: ON)
  -DUSE_AVX2=ON/OFF          Enable AVX2 SIMD (default: ON)
  -DBUILD_SHARED_LIBS=ON/OFF Build shared library (default: ON)
  -DBUILD_STATIC_LIBS=ON/OFF Build static library (default: OFF)
  -DBUILD_TESTS=ON/OFF       Build test executables (default: ON)
  -DCMAKE_BUILD_TYPE=...     Debug, Release, RelWithDebInfo
  -DCMAKE_INSTALL_PREFIX=... Installation prefix (default: /usr/local)
```

Example configurations:
```bash
# Optimized build with BLAS
cmake -DCMAKE_BUILD_TYPE=Release -DUSE_BLAS=ON ..

# Debug build without BLAS
cmake -DCMAKE_BUILD_TYPE=Debug -DUSE_BLAS=OFF ..

# Build both static and shared
cmake -DBUILD_SHARED_LIBS=ON -DBUILD_STATIC_LIBS=ON ..

# Install to custom prefix
cmake -DCMAKE_INSTALL_PREFIX=$HOME/.local ..
```

## Building Language Bindings

### Python Bindings

Python bindings use the C library via ctypes (no build needed):

```bash
# Ensure C library is built
cd atlas && make

# Set library path
export LD_LIBRARY_PATH="${PWD}/atlas/lib:$LD_LIBRARY_PATH"

# Test Python bindings
python3 -c "from bindings.python.atlas_bridge._native_ctx import AtlasContext; print('OK')"
```

### Rust Bindings

```bash
cd bindings/rust/atlas_bridge

# Build
cargo build --release

# Run tests
cargo test

# Note: Ensure atlas library is built and in library path
export LD_LIBRARY_PATH="$PWD/../../../atlas/lib:$LD_LIBRARY_PATH"
```

### Node.js Bindings

```bash
cd bindings/node/atlas_bridge

# Install dependencies
npm install

# Test
node -e "const {AtlasContext} = require('./index.js'); console.log('OK');"

# Note: Set library path
export LD_LIBRARY_PATH="$PWD/../../../atlas/lib:$LD_LIBRARY_PATH"
```

### Go Bindings

```bash
cd bindings/go/atlas_bridge

# Ensure library path is set
export LD_LIBRARY_PATH="$PWD/../../../atlas/lib:$LD_LIBRARY_PATH"
export CGO_LDFLAGS="-L$PWD/../../../atlas/lib"

# Build
go build

# Test
go test
```

## Artifact Files

### Required: lift_forms.hex

Create the lift forms file:

```bash
# Example lift forms
echo "A7 5C 39 D2 4E 11" > lift_forms.hex
```

Or use the example:
```bash
cp lift_forms.hex.example lift_forms.hex
```

### Optional: P_299_matrix.bin

This file is optional. If not present, the system uses fallback logic.

To generate (requires your implementation):
```python
import numpy as np

N = 12288
P_299 = generate_your_projector(N)  # Your implementation
P_299.astype(np.float64).tofile('P_299_matrix.bin')
```

### Optional: co1_gates.txt

Use the provided template or create your own:

```bash
# Use provided file
cat co1_gates.txt

# Or create custom configuration
cat > co1_gates.txt << 'EOF'
GENERATOR 0 PAGE_ROT 0
GENERATOR 1 PAGE_ROT 12
GENERATOR 2 PARITY_PHASE
GENERATOR 3 WALSH_MIX
EOF
```

## Testing

### Run All Tests

```bash
bash tools/verify_bridge.sh
```

### Run Individual Test Suites

```bash
cd atlas
make

# Build tests manually
gcc -o tests_ctx tests/tests_ctx.c src/atlas_bridge_ctx.c -Iinclude -lm
./tests_ctx

gcc -o tests_ctx_v03 tests/tests_ctx_v03.c src/atlas_bridge_ctx.c -Iinclude -lm
./tests_ctx_v03

gcc -o tests_ctx_v04 tests/tests_ctx_v04.c src/atlas_bridge_ctx.c -Iinclude -lm
./tests_ctx_v04
```

### Run CMake Tests

```bash
mkdir build && cd build
cmake -DBUILD_TESTS=ON ..
make
ctest --output-on-failure
```

## Installation

### System-wide Installation

```bash
cd atlas
sudo make install
# Installs to /usr/local/lib and /usr/local/include/atlas_bridge
```

### Custom Prefix

```bash
cd atlas
make install PREFIX=$HOME/.local
# Installs to ~/.local/lib and ~/.local/include/atlas_bridge

# Add to library path
export LD_LIBRARY_PATH="$HOME/.local/lib:$LD_LIBRARY_PATH"
```

### CMake Installation

```bash
mkdir build && cd build
cmake -DCMAKE_INSTALL_PREFIX=$HOME/.local ..
make
make install
```

## Troubleshooting

### Library Not Found

**Problem:** `libatlas_bridge_ctx.so: cannot open shared object file`

**Solution:**
```bash
# Add library directory to path
export LD_LIBRARY_PATH="${PWD}/atlas/lib:$LD_LIBRARY_PATH"

# Or install system-wide
cd atlas
sudo make install
sudo ldconfig
```

### BLAS Not Detected

**Problem:** Warning: `BLAS not found, using fallback naive loops`

**Solution:**
```bash
# Install BLAS libraries
sudo apt-get install libopenblas-dev  # Ubuntu/Debian
brew install openblas                  # macOS

# Verify detection
cd atlas
make clean
make
# Should see: "Found OpenBLAS via pkg-config" or "Found CBLAS headers"
```

### Compilation Errors

**Problem:** Compilation fails with errors

**Solutions:**

1. Check compiler version:
```bash
gcc --version  # Needs gcc 4.8+ for C11
```

2. Clean build:
```bash
cd atlas
make clean
make
```

3. Try without BLAS:
```bash
make USE_BLAS=no
```

### Test Failures

**Problem:** Tests fail during verification

**Check:**
1. Library built successfully
2. Artifact files present (lift_forms.hex)
3. No permission issues

**Debug:**
```bash
# Run tests with verbose output
cd build
ctest --verbose

# Or run individual test
./tests_ctx
```

## Continuous Integration

The repository includes `.github/workflows/bridge.yml` for automated builds and testing.

Local simulation:
```bash
# Run the same checks as CI
bash tools/verify_bridge.sh

# Check certificate
cat bridge_cert.json
```

## Performance Tuning

### Enable All Optimizations

```bash
cd atlas
make clean
CFLAGS="-O3 -march=native -mavx2" make USE_BLAS=yes
```

### Profile Performance

```bash
# Build with profiling
CFLAGS="-pg -O2" make

# Run and analyze
./your_program
gprof your_program gmon.out > analysis.txt
```

## Cross-Compilation

### For ARM
```bash
export CC=arm-linux-gnueabihf-gcc
cd atlas
make
```

### Using CMake Toolchain
```bash
cmake -DCMAKE_TOOLCHAIN_FILE=toolchain.cmake ..
make
```

## Next Steps

After building:

1. Read `MIGRATION_v0.5.md` for usage guide
2. Check `atlas/README_v04.md` for API documentation
3. Review examples in `bindings/*/atlas_bridge/`
4. Run `tools/verify_bridge.sh` to verify installation

## Support

For build issues:
- Check prerequisites are installed
- Review error messages carefully
- Try simpler configuration (no BLAS, no AVX2)
- Consult `atlas/README_v04.md` for detailed API docs
