// tests/tests_ctx_v04.c
// Atlas Bridge Context API v0.4 Extended Tests
// Conway–Monster Atlas Upgrade Kit
//
// Tests for v0.4 features:
// - P_299 exact matrix loader and fallback logic
// - Co1 real generator loader
// - AVX2 acceleration detection
// - Block-sparse mixing
// - 8-bit lift forms mode
// - Runtime lift forms swap

#include "../atlas/include/atlas_bridge_ctx.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <assert.h>

#define EPSILON 1e-6
#define BLOCK_SIZE 12288

// Helper: Generate random test vector
static void random_vector(double* v, size_t n, unsigned int seed) {
    srand(seed);
    for (size_t i = 0; i < n; i++) {
        v[i] = ((double)rand() / RAND_MAX) * 2.0 - 1.0;
    }
}

// Helper: Compute L2 norm
static double vec_norm(const double* v, size_t n) {
    double sum = 0.0;
    for (size_t i = 0; i < n; i++) {
        sum += v[i] * v[i];
    }
    return sqrt(sum);
}

// Helper: Vector difference norm
static double vec_diff(const double* a, const double* b, size_t n) {
    double sum = 0.0;
    for (size_t i = 0; i < n; i++) {
        double d = a[i] - b[i];
        sum += d * d;
    }
    return sqrt(sum);
}

// Test 1: P_299 fallback logic (no matrix loaded)
void test_p299_fallback(void) {
    printf("Test 1: P_299 fallback (reduced-rank trace-zero)...\n");
    
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    cfg.flags = ATLAS_CTX_ENABLE_P_299;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    assert(ctx != NULL);
    
    // Verify no exact matrix is loaded
    AtlasContextDiagnostics diag;
    atlas_ctx_get_diagnostics(ctx, &diag);
    assert(diag.p_299_exact_loaded == 0);
    printf("  ✓ No exact P_299 matrix loaded (fallback active)\n");
    
    // Test idempotency of fallback projector
    double* state = (double*)malloc(BLOCK_SIZE * sizeof(double));
    random_vector(state, BLOCK_SIZE, 42);
    
    double idem = atlas_ctx_check_p_299_idempotency(ctx, state);
    printf("  P_299 fallback idempotency: %.6e\n", idem);
    assert(idem < 1e-8);
    printf("  ✓ Fallback projector is idempotent\n");
    
    free(state);
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 2: P_299 exact matrix loader (create synthetic matrix)
void test_p299_exact_matrix(void) {
    printf("Test 2: P_299 exact matrix loader...\n");
    
    // Create a simple idempotent projector matrix for testing
    // For a small block size to keep test fast
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    cfg.block_size = 256;  // Smaller for test
    cfg.flags = ATLAS_CTX_ENABLE_P_299;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    assert(ctx != NULL);
    
    // Create a simple projector: constant rank-1 projector
    // P = (1/N) * 1 * 1^T projects onto constant vector
    size_t N = 256;
    double* matrix = (double*)malloc(N * N * sizeof(double));
    double scale = 1.0 / N;
    for (size_t i = 0; i < N; i++) {
        for (size_t j = 0; j < N; j++) {
            matrix[i * N + j] = scale;
        }
    }
    
    // Save to temporary file
    const char* temp_file = "/tmp/test_p299_matrix.bin";
    FILE* f = fopen(temp_file, "wb");
    assert(f != NULL);
    fwrite(matrix, sizeof(double), N * N, f);
    fclose(f);
    free(matrix);
    
    // Load the matrix
    int result = atlas_ctx_load_p299_matrix(ctx, temp_file);
    assert(result == 0);
    printf("  ✓ P_299 matrix loaded from file\n");
    
    // Verify diagnostics show exact matrix is loaded
    AtlasContextDiagnostics diag;
    atlas_ctx_get_diagnostics(ctx, &diag);
    assert(diag.p_299_exact_loaded == 1);
    printf("  ✓ Diagnostics confirm exact matrix loaded\n");
    
    // Test idempotency with exact matrix
    double* state = (double*)malloc(N * sizeof(double));
    random_vector(state, N, 123);
    
    double idem = atlas_ctx_check_p_299_idempotency(ctx, state);
    printf("  P_299 exact matrix idempotency: %.6e\n", idem);
    assert(idem < 1e-8);
    printf("  ✓ Exact matrix is idempotent\n");
    
    free(state);
    atlas_ctx_free(ctx);
    remove(temp_file);
    printf("  PASS\n\n");
}

// Test 3: Co1 real generator loader
void test_co1_gates_loader(void) {
    printf("Test 3: Co1 real generator loader...\n");
    
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    cfg.flags = ATLAS_CTX_ENABLE_CO1;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    assert(ctx != NULL);
    
    // Create a simple co1_gates.txt file
    const char* temp_file = "/tmp/test_co1_gates.txt";
    FILE* f = fopen(temp_file, "w");
    assert(f != NULL);
    fprintf(f, "# Co1 Real Generators Test File\n");
    fprintf(f, "1.0\n");
    fprintf(f, "0.707\n");
    fprintf(f, "0.5\n");
    fprintf(f, "# Comment line\n");
    fprintf(f, "0.866\n");
    fclose(f);
    
    // Load the gates
    int result = atlas_ctx_load_co1_gates(ctx, temp_file);
    assert(result == 0);
    printf("  ✓ Co1 gates loaded from file\n");
    
    // Verify diagnostics
    AtlasContextDiagnostics diag;
    atlas_ctx_get_diagnostics(ctx, &diag);
    assert(diag.co1_gates_loaded == 1);
    printf("  ✓ Diagnostics confirm Co1 gates loaded\n");
    
    atlas_ctx_free(ctx);
    remove(temp_file);
    printf("  PASS\n\n");
}

// Test 4: AVX2 detection
void test_avx2_detection(void) {
    printf("Test 4: AVX2 detection...\n");
    
    // Test without AVX2 flag
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    assert(ctx != NULL);
    
    int avx2_active = atlas_ctx_is_avx2_active(ctx);
    printf("  AVX2 active (without flag): %d\n", avx2_active);
    assert(avx2_active == 0);
    printf("  ✓ AVX2 disabled when flag not set\n");
    
    atlas_ctx_free(ctx);
    
    // Test with AVX2 flag
    cfg.flags = ATLAS_CTX_USE_AVX2;
    ctx = atlas_ctx_new(&cfg);
    assert(ctx != NULL);
    
    avx2_active = atlas_ctx_is_avx2_active(ctx);
    printf("  AVX2 active (with flag): %d\n", avx2_active);
    // Note: Will be 1 only if compiled with AVX2 support
#if defined(__AVX2__) && defined(__x86_64__)
    assert(avx2_active == 1);
    printf("  ✓ AVX2 enabled (compiled with AVX2 support)\n");
#else
    assert(avx2_active == 0);
    printf("  ✓ AVX2 not available (not compiled with AVX2 support)\n");
#endif
    
    // Check diagnostics
    AtlasContextDiagnostics diag;
    atlas_ctx_get_diagnostics(ctx, &diag);
    assert(diag.avx2_available == avx2_active);
    printf("  ✓ Diagnostics match AVX2 status\n");
    
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 5: Block-sparse mixing
void test_block_mixing(void) {
    printf("Test 5: Block-sparse mixing (8x8 matrix)...\n");
    
    AtlasBridgeContext* ctx = atlas_ctx_new_default();
    assert(ctx != NULL);
    
    // Create test state
    double* state = (double*)malloc(BLOCK_SIZE * sizeof(double));
    for (size_t i = 0; i < BLOCK_SIZE; i++) {
        state[i] = (double)(i % 8);
    }
    
    // Create identity mixing matrix (should leave block unchanged)
    double mixing[64];
    for (int i = 0; i < 8; i++) {
        for (int j = 0; j < 8; j++) {
            mixing[i * 8 + j] = (i == j) ? 1.0 : 0.0;
        }
    }
    
    // Save original first block
    double orig_block[8];
    for (int i = 0; i < 8; i++) {
        orig_block[i] = state[i];
    }
    
    // Apply identity mixing to block 0
    int result = atlas_ctx_apply_block_mixing(ctx, 0, mixing, state);
    assert(result == 0);
    printf("  ✓ Block mixing applied\n");
    
    // Verify block unchanged (identity matrix)
    for (int i = 0; i < 8; i++) {
        assert(fabs(state[i] - orig_block[i]) < EPSILON);
    }
    printf("  ✓ Identity mixing preserves block\n");
    
    // Test with permutation matrix (reverse order)
    for (int i = 0; i < 8; i++) {
        for (int j = 0; j < 8; j++) {
            mixing[i * 8 + j] = (i + j == 7) ? 1.0 : 0.0;
        }
    }
    
    result = atlas_ctx_apply_block_mixing(ctx, 0, mixing, state);
    assert(result == 0);
    
    // Verify block reversed
    for (int i = 0; i < 8; i++) {
        assert(fabs(state[i] - orig_block[7 - i]) < EPSILON);
    }
    printf("  ✓ Permutation mixing works correctly\n");
    
    free(state);
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 6: 8-bit lift forms mode
void test_lift_8bit_mode(void) {
    printf("Test 6: 8-bit lift forms mode...\n");
    
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    cfg.flags = ATLAS_CTX_ENABLE_LIFT | ATLAS_CTX_LIFT_8BIT;
    cfg.n_qbits = 8;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    assert(ctx != NULL);
    
    // Verify config
    AtlasContextConfig retrieved;
    atlas_ctx_get_config(ctx, &retrieved);
    assert(retrieved.n_qbits == 8);
    assert(retrieved.flags & ATLAS_CTX_LIFT_8BIT);
    printf("  ✓ 8-bit mode configured\n");
    
    // Set small lift forms data (only low 8 bits used)
    const char* hex_data = "0102030405060708";
    int result = atlas_ctx_set_lift_forms_hex(ctx, hex_data, strlen(hex_data));
    assert(result == 0);
    printf("  ✓ Lift forms set in 8-bit mode\n");
    
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 7: Runtime lift forms swap
void test_lift_forms_swap(void) {
    printf("Test 7: Runtime lift forms swap...\n");
    
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    cfg.flags = ATLAS_CTX_ENABLE_LIFT;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    assert(ctx != NULL);
    
    // Set initial lift forms
    const char* hex1 = "deadbeef";
    int result = atlas_ctx_set_lift_forms_hex(ctx, hex1, strlen(hex1));
    assert(result == 0);
    printf("  ✓ Initial lift forms set\n");
    
    // Retrieve and verify
    char* retrieved1 = atlas_ctx_get_lift_forms_hex(ctx);
    assert(retrieved1 != NULL);
    assert(strcmp(retrieved1, hex1) == 0);
    printf("  ✓ Lift forms retrieved correctly\n");
    free(retrieved1);
    
    // Swap to new lift forms
    const char* hex2 = "cafebabe";
    result = atlas_ctx_set_lift_forms_hex(ctx, hex2, strlen(hex2));
    assert(result == 0);
    printf("  ✓ Lift forms swapped at runtime\n");
    
    // Verify swap
    char* retrieved2 = atlas_ctx_get_lift_forms_hex(ctx);
    assert(retrieved2 != NULL);
    assert(strcmp(retrieved2, hex2) == 0);
    printf("  ✓ Swapped lift forms verified\n");
    free(retrieved2);
    
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 8: Certificate emission with v0.4 fields
void test_certificate_v04(void) {
    printf("Test 8: Certificate emission with v0.4 fields...\n");
    
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    cfg.flags = ATLAS_CTX_ENABLE_P_299 | ATLAS_CTX_ENABLE_CO1 | ATLAS_CTX_USE_AVX2;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    assert(ctx != NULL);
    
    // Emit certificate
    const char* cert_file = "/tmp/test_cert_v04.json";
    int result = atlas_ctx_emit_certificate(ctx, cert_file, "test_v04");
    assert(result == 0);
    printf("  ✓ Certificate emitted\n");
    
    // Read and verify it contains v0.4 fields
    FILE* f = fopen(cert_file, "r");
    assert(f != NULL);
    
    char buffer[4096];
    size_t read_size = fread(buffer, 1, sizeof(buffer) - 1, f);
    buffer[read_size] = '\0';
    fclose(f);
    
    // Check for v0.5 fields (updated from v0.4)
    assert(strstr(buffer, "\"version\": \"0.5.0\"") != NULL);
    assert(strstr(buffer, "avx2_available") != NULL);
    assert(strstr(buffer, "p_299_exact_loaded") != NULL);
    assert(strstr(buffer, "co1_gates_loaded") != NULL);
    printf("  ✓ Certificate contains v0.5 fields\n");
    
    atlas_ctx_free(ctx);
    remove(cert_file);
    printf("  PASS\n\n");
}

// Main test driver
int main(void) {
    printf("=== Atlas Bridge Context API v0.4 Tests ===\n\n");
    
    test_p299_fallback();
    test_p299_exact_matrix();
    test_co1_gates_loader();
    test_avx2_detection();
    test_block_mixing();
    test_lift_8bit_mode();
    test_lift_forms_swap();
    test_certificate_v04();
    
    printf("=== All v0.4 tests passed! ===\n");
    return 0;
}
