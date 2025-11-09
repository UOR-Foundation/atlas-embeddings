#!/bin/bash
# tools/verify_bridge.sh
# Atlas Bridge Deployment Pack v0.5
# Full verification suite with cert check and metrics threshold enforcement

set -e  # Exit on error

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Configuration
ATLAS_CORE_DIR="${ATLAS_CORE_DIR:-atlas_core}"
BUILD_DIR="${BUILD_DIR:-build}"
CERT_FILE="${CERT_FILE:-bridge_cert.json}"
TESTS_DIR="${TESTS_DIR:-tests}"

# Thresholds (as specified in deployment pack v0.5)
THRESHOLD_P_CLASS_IDEMP=1e-8        # Target: 1e-8, practice: 1e-12
THRESHOLD_P_299_IDEMP=1e-8
THRESHOLD_COMMUTANT_DIM=1.5         # Effective dim of Comm(E,Co1)

# Detect BLAS availability
detect_blas() {
    echo -e "${YELLOW}[INFO]${NC} Detecting BLAS libraries..."
    
    BLAS_FLAGS=""
    BLAS_LIBS=""
    
    # Try OpenBLAS first
    if pkg-config --exists openblas 2>/dev/null; then
        echo -e "${GREEN}[OK]${NC} Found OpenBLAS via pkg-config"
        BLAS_FLAGS=$(pkg-config --cflags openblas)
        BLAS_LIBS=$(pkg-config --libs openblas)
        BLAS_FOUND="openblas"
    elif [ -f /usr/include/cblas.h ] || [ -f /usr/local/include/cblas.h ]; then
        echo -e "${GREEN}[OK]${NC} Found CBLAS headers"
        BLAS_LIBS="-lcblas -lblas"
        BLAS_FOUND="cblas"
    else
        echo -e "${YELLOW}[WARN]${NC} BLAS not found, using fallback naive loops"
        BLAS_FOUND="none"
    fi
    
    export BLAS_FLAGS BLAS_LIBS BLAS_FOUND
}

# Compile atlas_bridge_ctx library with BLAS support
build_library() {
    echo -e "${YELLOW}[INFO]${NC} Building atlas_bridge_ctx library..."
    
    mkdir -p "$ATLAS_CORE_DIR/lib"
    
    # Detect AVX2 support
    AVX2_FLAGS=""
    if grep -q avx2 /proc/cpuinfo 2>/dev/null; then
        echo -e "${GREEN}[OK]${NC} AVX2 support detected"
        AVX2_FLAGS="-mavx2"
    else
        echo -e "${YELLOW}[WARN]${NC} AVX2 not available, using scalar fallback"
    fi
    
    # Compile with BLAS if available
    CFLAGS="-O2 -Wall -fPIC $AVX2_FLAGS $BLAS_FLAGS"
    
    if [ "$BLAS_FOUND" != "none" ]; then
        CFLAGS="$CFLAGS -DUSE_BLAS"
        echo -e "${GREEN}[OK]${NC} Compiling with BLAS acceleration"
    fi
    
    gcc $CFLAGS -c -I"$ATLAS_CORE_DIR/include" \
        "$ATLAS_CORE_DIR/src/atlas_bridge_ctx.c" \
        -o "$BUILD_DIR/atlas_bridge_ctx.o"
    
    # Create shared library
    gcc -shared -o "$ATLAS_CORE_DIR/lib/libatlas_bridge_ctx.so" \
        "$BUILD_DIR/atlas_bridge_ctx.o" -lm $BLAS_LIBS
    
    echo -e "${GREEN}[OK]${NC} Library built: $ATLAS_CORE_DIR/lib/libatlas_bridge_ctx.so"
}

# Compile test executables
build_tests() {
    echo -e "${YELLOW}[INFO]${NC} Building test executables..."
    
    CFLAGS="-O2 -Wall -I$ATLAS_CORE_DIR/include"
    
    if [ "$BLAS_FOUND" != "none" ]; then
        CFLAGS="$CFLAGS -DUSE_BLAS"
    fi
    
    # Build main test suites
    for test_file in tests_ctx tests_ctx_v03 tests_ctx_v04; do
        if [ -f "$TESTS_DIR/${test_file}.c" ]; then
            gcc $CFLAGS -o "$BUILD_DIR/$test_file" \
                "$TESTS_DIR/${test_file}.c" \
                "$ATLAS_CORE_DIR/src/atlas_bridge_ctx.c" \
                -lm $BLAS_LIBS
            echo -e "${GREEN}[OK]${NC} Built $test_file"
        fi
    done
    
    # Build cert generator
    cat > "$BUILD_DIR/cert_generator.c" << 'EOF'
#include "atlas_bridge_ctx.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char** argv) {
    const char* cert_path = argc > 1 ? argv[1] : "bridge_cert.json";
    
    // Create context with all features enabled
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    cfg.flags = ATLAS_CTX_ENABLE_TWIRL | ATLAS_CTX_ENABLE_P_CLASS | 
                ATLAS_CTX_ENABLE_P_299 | ATLAS_CTX_ENABLE_CO1 | 
                ATLAS_CTX_USE_AVX2 | ATLAS_CTX_LIFT_8BIT;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    if (!ctx) {
        fprintf(stderr, "Failed to create context\n");
        return 1;
    }
    
    // Load lift forms if available
    if (atlas_ctx_load_lift_forms(ctx, "lift_forms.hex") == 0) {
        printf("Loaded lift forms from lift_forms.hex\n");
    } else {
        printf("Using default lift forms\n");
    }
    
    // Try to load P_299 matrix if available
    if (atlas_ctx_load_p299_matrix(ctx, "P_299_matrix.bin") == 0) {
        printf("Loaded exact P_299 matrix\n");
    } else {
        printf("Using P_299 fallback logic\n");
    }
    
    // Try to load Co1 gates if available
    if (atlas_ctx_load_co1_gates(ctx, "co1_gates.txt") == 0) {
        printf("Loaded Co1 gates configuration\n");
    } else {
        printf("Using default Co1 gates\n");
    }
    
    // Allocate test state
    uint32_t block_size = atlas_ctx_get_block_size(ctx);
    double* state = malloc(block_size * sizeof(double));
    if (!state) {
        fprintf(stderr, "Failed to allocate state vector\n");
        atlas_ctx_free(ctx);
        return 1;
    }
    
    // Initialize with random-ish values
    for (uint32_t i = 0; i < block_size; i++) {
        state[i] = (double)i / (double)block_size;
    }
    
    // Run diagnostics
    printf("Running diagnostics...\n");
    
    // Check P_class idempotency
    atlas_ctx_apply_p_class(ctx, state);
    double p_class_idemp = atlas_ctx_check_p_class_idempotency(ctx, state);
    printf("P_class idempotency: %.2e\n", p_class_idemp);
    
    // Check P_299 idempotency
    atlas_ctx_apply_p_299(ctx, state);
    double p_299_idemp = atlas_ctx_check_p_299_idempotency(ctx, state);
    printf("P_299 idempotency: %.2e\n", p_299_idemp);
    
    // Probe commutant
    double comm_dim = atlas_ctx_probe_commutant(ctx, state, 1);
    printf("Commutant effective dim: %.4f\n", comm_dim);
    
    // Emit certificate
    if (atlas_ctx_emit_certificate(ctx, cert_path, "verify_bridge") == 0) {
        printf("Certificate written to %s\n", cert_path);
    } else {
        fprintf(stderr, "Failed to write certificate\n");
        free(state);
        atlas_ctx_free(ctx);
        return 1;
    }
    
    free(state);
    atlas_ctx_free(ctx);
    return 0;
}
EOF
    
    gcc $CFLAGS -o "$BUILD_DIR/cert_generator" \
        "$BUILD_DIR/cert_generator.c" \
        "$ATLAS_CORE_DIR/src/atlas_bridge_ctx.c" \
        -lm $BLAS_LIBS
    
    echo -e "${GREEN}[OK]${NC} Built cert_generator"
}

# Run unit tests
run_tests() {
    echo -e "${YELLOW}[INFO]${NC} Running unit tests..."
    
    FAILED=0
    
    for test_exe in tests_ctx tests_ctx_v03 tests_ctx_v04; do
        if [ -f "$BUILD_DIR/$test_exe" ]; then
            echo -e "${YELLOW}[TEST]${NC} Running $test_exe..."
            if "$BUILD_DIR/$test_exe"; then
                echo -e "${GREEN}[PASS]${NC} $test_exe"
            else
                echo -e "${RED}[FAIL]${NC} $test_exe"
                FAILED=1
            fi
        fi
    done
    
    if [ $FAILED -ne 0 ]; then
        echo -e "${RED}[ERROR]${NC} Some tests failed"
        exit 1
    fi
    
    echo -e "${GREEN}[OK]${NC} All unit tests passed"
}

# Generate and verify certificate
generate_certificate() {
    echo -e "${YELLOW}[INFO]${NC} Generating certificate..."
    
    "$BUILD_DIR/cert_generator" "$CERT_FILE"
    
    if [ ! -f "$CERT_FILE" ]; then
        echo -e "${RED}[ERROR]${NC} Certificate not generated"
        exit 1
    fi
    
    echo -e "${GREEN}[OK]${NC} Certificate generated: $CERT_FILE"
}

# Verify metrics against thresholds
verify_metrics() {
    echo -e "${YELLOW}[INFO]${NC} Verifying metrics against thresholds..."
    
    if [ ! -f "$CERT_FILE" ]; then
        echo -e "${RED}[ERROR]${NC} Certificate file not found: $CERT_FILE"
        exit 1
    fi
    
    # Extract metrics from JSON (using grep/sed for simplicity)
    P_CLASS_IDEMP=$(grep -oP '"p_class_idempotency":\s*\K[0-9.e+-]+' "$CERT_FILE" || echo "0")
    P_299_IDEMP=$(grep -oP '"p_299_idempotency":\s*\K[0-9.e+-]+' "$CERT_FILE" || echo "0")
    COMM_DIM=$(grep -oP '"commutant_dim":\s*\K[0-9.e+-]+' "$CERT_FILE" || echo "0")
    
    echo "Extracted metrics:"
    echo "  P_class idempotency: $P_CLASS_IDEMP (threshold: $THRESHOLD_P_CLASS_IDEMP)"
    echo "  P_299 idempotency: $P_299_IDEMP (threshold: $THRESHOLD_P_299_IDEMP)"
    echo "  Commutant dim: $COMM_DIM (threshold: < $THRESHOLD_COMMUTANT_DIM)"
    
    # Simple threshold checks using awk (handles scientific notation)
    PASS=1
    
    # AWK handles scientific notation natively, but we verify with explicit conversion
    if ! awk -v val="$P_CLASS_IDEMP" -v thr="$THRESHOLD_P_CLASS_IDEMP" 'BEGIN { exit !(val+0 <= thr+0) }'; then
        echo -e "${RED}[FAIL]${NC} P_class idempotency exceeds threshold"
        PASS=0
    else
        echo -e "${GREEN}[PASS]${NC} P_class idempotency within threshold"
    fi
    
    if ! awk -v val="$P_299_IDEMP" -v thr="$THRESHOLD_P_299_IDEMP" 'BEGIN { exit !(val+0 <= thr+0) }'; then
        echo -e "${RED}[FAIL]${NC} P_299 idempotency exceeds threshold"
        PASS=0
    else
        echo -e "${GREEN}[PASS]${NC} P_299 idempotency within threshold"
    fi
    
    if ! awk -v val="$COMM_DIM" -v thr="$THRESHOLD_COMMUTANT_DIM" 'BEGIN { exit !(val+0 < thr+0) }'; then
        echo -e "${RED}[FAIL]${NC} Commutant dimension exceeds threshold"
        PASS=0
    else
        echo -e "${GREEN}[PASS]${NC} Commutant dimension within threshold"
    fi
    
    if [ $PASS -ne 1 ]; then
        echo -e "${RED}[ERROR]${NC} Metrics verification failed"
        exit 1
    fi
    
    echo -e "${GREEN}[OK]${NC} All metrics within thresholds"
}

# Main execution
main() {
    echo "=========================================="
    echo "Atlas Bridge Verification Suite v0.5"
    echo "=========================================="
    echo ""
    
    # Create build directory
    mkdir -p "$BUILD_DIR"
    
    # Run verification steps
    detect_blas
    build_library
    build_tests
    run_tests
    generate_certificate
    verify_metrics
    
    echo ""
    echo "=========================================="
    echo -e "${GREEN}[SUCCESS]${NC} Bridge verification complete!"
    echo "=========================================="
    echo ""
    echo "Certificate: $CERT_FILE"
    echo "BLAS: $BLAS_FOUND"
    echo ""
}

# Run main
main "$@"
