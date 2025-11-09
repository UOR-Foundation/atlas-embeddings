#!/usr/bin/env bash
set -euo pipefail

# Update FFI Bindings Script
# Copies the compiled FFI library to all language binding directories
# Run this after: cargo build --release -p hologram-ffi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "🔄 Updating FFI bindings..."

# Determine library extension based on platform
if [[ "$OSTYPE" == "darwin"* ]]; then
    LIB_EXT="dylib"
elif [[ "$OSTYPE" == "msys" || "$OSTYPE" == "win32" ]]; then
    LIB_EXT="dll"
else
    LIB_EXT="so"
fi

# Check if release library exists
RELEASE_LIB="target/release/libhologram_ffi.$LIB_EXT"
DEBUG_LIB="target/debug/libhologram_ffi.$LIB_EXT"

if [[ -f "$RELEASE_LIB" ]]; then
    SOURCE_LIB="$RELEASE_LIB"
    echo "✓ Using release build: $RELEASE_LIB"
elif [[ -f "$DEBUG_LIB" ]]; then
    SOURCE_LIB="$DEBUG_LIB"
    echo "⚠️  Using debug build: $DEBUG_LIB"
    echo "   (Run 'cargo build --release -p hologram-ffi' for better performance)"
else
    echo "❌ Error: libhologram_ffi.$LIB_EXT not found in target/release or target/debug"
    echo "   Run: cargo build --release -p hologram-ffi"
    exit 1
fi

# Copy to Python bindings
PYTHON_DEST="crates/hologram-ffi/interfaces/python/hologram_ffi/libuniffi_hologram_ffi.$LIB_EXT"
echo "📦 Copying to Python bindings: $PYTHON_DEST"
cp -v "$SOURCE_LIB" "$PYTHON_DEST"

# Copy to TypeScript bindings (if needed)
# TYPESCRIPT_DEST="crates/hologram-ffi/interfaces/typescript/libuniffi_hologram_ffi.$LIB_EXT"
# if [[ -d "crates/hologram-ffi/interfaces/typescript" ]]; then
#     echo "📦 Copying to TypeScript bindings: $TYPESCRIPT_DEST"
#     cp -v "$SOURCE_LIB" "$TYPESCRIPT_DEST"
# fi

echo ""
echo "✅ FFI bindings updated successfully!"
echo ""
echo "📝 Note: This script only copies the compiled library."
echo "   To regenerate binding code, run:"
echo "   cargo run --bin generate_bindings --manifest-path crates/hologram-ffi/Cargo.toml"
