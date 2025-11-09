#!/bin/bash
# Hologram FFI Library Rebuild Script
# Usage: ./rebuild.sh [--release] [--test] [--help]

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Default values
BUILD_TYPE="debug"
RUN_TESTS=false
CLEAN=true

# Get the root directory of the workspace (3 levels up from this script)
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/../../.." && pwd)"

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --release|-r)
            BUILD_TYPE="release"
            shift
            ;;
        --test|-t)
            RUN_TESTS=true
            shift
            ;;
        --no-clean)
            CLEAN=false
            shift
            ;;
        --help|-h)
            echo "Hologram FFI Library Rebuild Script"
            echo ""
            echo "Usage: $0 [OPTIONS]"
            echo ""
            echo "Options:"
            echo "  --release, -r     Build in release mode (default: debug)"
            echo "  --test, -t         Run tests after rebuild"
            echo "  --no-clean         Skip cleaning previous build"
            echo "  --help, -h         Show this help message"
            echo ""
            echo "Examples:"
            echo "  $0                 # Debug build, no tests"
            echo "  $0 --release       # Release build, no tests"
            echo "  $0 --test          # Debug build with tests"
            echo "  $0 --release --test # Release build with tests"
            exit 0
            ;;
        *)
            echo -e "${RED}Unknown option: $1${NC}"
            echo "Use --help for usage information"
            exit 1
            ;;
    esac
done

echo -e "${BLUE}🚀 Hologram FFI Library Rebuild${NC}"
echo -e "${BLUE}================================${NC}"
echo -e "Build type: ${YELLOW}$BUILD_TYPE${NC}"
echo -e "Run tests: ${YELLOW}$RUN_TESTS${NC}"
echo ""

cd "$ROOT_DIR/crates/hologram-ffi"

# Step 1: Clean (if requested)
if [ "$CLEAN" = true ]; then
    echo -e "${YELLOW}🧹 Cleaning previous build...${NC}"
    cargo clean
    echo -e "${GREEN}✅ Clean completed${NC}"
fi

# Step 2: Build library
echo -e "${YELLOW}🔨 Building library ($BUILD_TYPE)...${NC}"
if [ "$BUILD_TYPE" = "release" ]; then
    cargo build --release
    LIBRARY_PATH="$ROOT_DIR/target/release/libhologram_ffi.so"
else
    cargo build
    LIBRARY_PATH="$ROOT_DIR/target/debug/libhologram_ffi.so"
fi
echo -e "${GREEN}✅ Library built successfully${NC}"

# Step 3: Update bindings generator
echo -e "${YELLOW}🔄 Updating bindings generator...${NC}"
if [ "$BUILD_TYPE" = "release" ]; then
    sed -i "s|target/debug/libhologram_ffi.so|$ROOT_DIR/target/release/libhologram_ffi.so|g" generate_bindings.rs
else
    sed -i "s|target/release/libhologram_ffi.so|$ROOT_DIR/target/debug/libhologram_ffi.so|g" generate_bindings.rs
fi

# Step 4: Generate bindings
echo -e "${YELLOW}🔄 Generating Python bindings...${NC}"
cargo run --bin generate-bindings
echo -e "${GREEN}✅ Bindings generated${NC}"

# Step 5: Update Python package
echo -e "${YELLOW}📦 Updating Python package...${NC}"
cp "$LIBRARY_PATH" interfaces/python/hologram_ffi/libuniffi_hologram_ffi.so
cp interfaces/python/hologram_ffi.py interfaces/python/hologram_ffi/hologram_ffi.py
cd interfaces/python
pip install -e . --force-reinstall
echo -e "${GREEN}✅ Python package updated${NC}"

# Step 6: Update TypeScript package
echo -e "${YELLOW}📦 Updating TypeScript package...${NC}"
cd ../typescript
npm install
echo -e "${GREEN}✅ TypeScript package updated${NC}"

# Step 7: Run tests (if requested)
if [ "$RUN_TESTS" = true ]; then
    echo ""
    echo -e "${YELLOW}🧪 Running tests...${NC}"

    # Test Rust
    echo -e "${BLUE}Testing Rust bindings...${NC}"
    cargo test --test unit_tests
    cargo test --test integration_tests
    cargo test --test compile_test
    echo -e "${GREEN}✅ Rust tests passed${NC}"
    
    # Test Python
    echo -e "${BLUE}Testing Python bindings...${NC}"
    cd ../python
    python3 -c "
import hologram_ffi as hg
try:
    status = hg.get_registry_status()
    print(f'✅ get_registry_status: {status}')
    hg.clear_all_registries()
    print('✅ clear_all_registries works')
    executor_handle = hg.new_executor()
    print(f'✅ new_executor: {executor_handle}')
    hg.executor_cleanup(executor_handle)
    print('✅ executor_cleanup works')
    print('🎉 Python tests passed!')
except Exception as e:
    print(f'❌ Python test failed: {e}')
    exit(1)
"
    
    # Test TypeScript
    echo -e "${BLUE}Testing TypeScript bindings...${NC}"
    cd ../typescript
    npm test --silent
    echo -e "${GREEN}✅ TypeScript tests passed${NC}"
fi

echo ""
echo -e "${GREEN}🎉 Rebuild completed successfully!${NC}"
echo -e "${GREEN}================================${NC}"
echo -e "Build type: ${YELLOW}$BUILD_TYPE${NC}"
echo -e "Library: ${YELLOW}$LIBRARY_PATH${NC}"
echo ""
echo -e "${BLUE}Manual test commands:${NC}"
echo -e "  Python: ${YELLOW}cd interfaces/python && python -m pytest tests -v${NC}"
echo -e "  TypeScript: ${YELLOW}cd interfaces/typescript && npm test${NC}"
echo -e "  Rust: ${YELLOW}cargo test -- --nocapture --color=always${NC}"
