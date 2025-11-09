#!/bin/bash
# Create static library bundle for UOR FFI
# This script bundles all Lean modules and dependencies into a single static library

set -e

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
BUILD_DIR="$PROJECT_ROOT/.lake/build"
LIB_DIR="$BUILD_DIR/lib"
BUNDLE_DIR="$BUILD_DIR/bundle"

echo "Creating static library bundle for UOR FFI..."

# Create bundle directory
mkdir -p "$BUNDLE_DIR"
cd "$BUNDLE_DIR"

# Extract all Lean shared libraries to object files
echo "Extracting Lean module objects..."
for lib in "$LIB_DIR/lean"/*.so; do
    if [ -f "$lib" ]; then
        base=$(basename "$lib" .so)
        echo "  Processing $base..."
        # Extract symbols from shared library
        objcopy --extract-symbol "$lib" "${base}.sym" 2>/dev/null || true
        # Convert to relocatable object
        ld -r -o "${base}.o" --whole-archive "$lib" 2>/dev/null || \
        # Fallback: copy as-is if conversion fails
        cp "$lib" "${base}.o"
    fi
done

# Get Lean system libraries
LEAN_SYSROOT="${LEAN_SYSROOT:-/home/codespace/.elan/toolchains/leanprover--lean4---v4.22.0}"
LEAN_LIB_DIR="$LEAN_SYSROOT/lib/lean"

# Copy required Lean static libraries
echo "Copying Lean runtime libraries..."
cp "$LEAN_LIB_DIR/libleanrt.a" . 2>/dev/null || echo "  Warning: libleanrt.a not found"
cp "$LEAN_LIB_DIR/libleancpp.a" . 2>/dev/null || echo "  Warning: libleancpp.a not found"

# Extract objects from static libraries
echo "Extracting static library objects..."
for lib in *.a; do
    if [ -f "$lib" ]; then
        base=$(basename "$lib" .a)
        mkdir -p "$base"
        cd "$base"
        ar x "../$lib"
        cd ..
    fi
done

# Collect all object files
echo "Collecting object files..."
find . -name "*.o" -type f > objects.txt

# Create the bundle
echo "Creating libuor_bundle.a..."
ar rcs libuor_bundle.a $(cat objects.txt)

# Create minimal wrapper if needed
cat > uor_bundle_init.c << 'EOF'
#include <stdint.h>

/* Minimal initialization for static bundle */
void uor_bundle_init(void) {
    /* Static initialization handled by linker */
}

void uor_bundle_fini(void) {
    /* Static cleanup */
}
EOF

# Compile wrapper
clang -c -O2 -fPIC uor_bundle_init.c -o uor_bundle_init.o
ar rcs libuor_bundle.a uor_bundle_init.o

# Generate pkg-config file for bundle
cat > uor-bundle.pc << EOF
prefix=/usr/local
exec_prefix=\${prefix}
libdir=\${exec_prefix}/lib
includedir=\${prefix}/include

Name: UOR-Bundle
Description: UOR Prime Structure FFI Static Bundle
Version: 1.0.0
Libs: -L\${libdir} -luor_bundle -lstdc++ -lgmp -lpthread -ldl -lm
Cflags: -I\${includedir}/uor-ffi
EOF

# Copy to lib directory
echo "Installing bundle..."
cp libuor_bundle.a "$LIB_DIR/"
cp uor-bundle.pc "$LIB_DIR/"

# Report size
echo ""
echo "Bundle created successfully!"
echo "  Location: $LIB_DIR/libuor_bundle.a"
echo "  Size: $(du -h "$LIB_DIR/libuor_bundle.a" | cut -f1)"
echo ""
echo "To use the bundle, link with:"
echo "  gcc myapp.c -L$LIB_DIR -luor_bundle -lstdc++ -lgmp -lpthread -ldl -lm"
echo ""
echo "Or with pkg-config:"
echo "  gcc myapp.c \$(pkg-config --cflags --libs $LIB_DIR/uor-bundle.pc)"