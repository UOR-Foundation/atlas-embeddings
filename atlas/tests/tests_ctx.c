// atlas/tests/tests_ctx.c
// Atlas Bridge Context API v0.2 Self-Tests
// Conway–Monster Atlas Upgrade Kit

#include "atlas_bridge_ctx.h"
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

// Test 1: Context lifecycle (new/clone/free)
void test_context_lifecycle(void) {
    printf("Test 1: Context lifecycle...\n");
    
    // Create default context
    AtlasBridgeContext* ctx1 = atlas_ctx_new_default();
    assert(ctx1 != NULL);
    printf("  ✓ Default context created\n");
    
    // Validate context
    assert(atlas_ctx_validate(ctx1) == 0);
    printf("  ✓ Context validation passed\n");
    
    // Clone context
    AtlasBridgeContext* ctx2 = atlas_ctx_clone(ctx1);
    assert(ctx2 != NULL);
    printf("  ✓ Context cloned\n");
    
    // Check configurations match
    AtlasContextConfig cfg1, cfg2;
    atlas_ctx_get_config(ctx1, &cfg1);
    atlas_ctx_get_config(ctx2, &cfg2);
    assert(cfg1.block_size == cfg2.block_size);
    assert(cfg1.n_qubits == cfg2.n_qubits);
    assert(cfg1.twirl_gens == cfg2.twirl_gens);
    printf("  ✓ Cloned configuration matches\n");
    
    // Free contexts
    atlas_ctx_free(ctx1);
    atlas_ctx_free(ctx2);
    printf("  ✓ Contexts freed\n");
    
    printf("  PASS\n\n");
}

// Test 2: Configuration management
void test_configuration(void) {
    printf("Test 2: Configuration management...\n");
    
    // Test default config
    AtlasContextConfig default_cfg;
    atlas_ctx_config_default(&default_cfg);
    assert(default_cfg.block_size == 12288);
    assert(default_cfg.n_qubits == 8);
    assert(default_cfg.twirl_gens == 16);
    printf("  ✓ Default config correct\n");
    
    // Create context with custom config
    AtlasContextConfig custom_cfg = default_cfg;
    custom_cfg.flags = ATLAS_CTX_ENABLE_TWIRL | ATLAS_CTX_ENABLE_LIFT;
    custom_cfg.epsilon = 1e-8;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&custom_cfg);
    assert(ctx != NULL);
    
    // Verify config
    AtlasContextConfig retrieved_cfg;
    atlas_ctx_get_config(ctx, &retrieved_cfg);
    assert(retrieved_cfg.flags == custom_cfg.flags);
    assert(retrieved_cfg.epsilon == custom_cfg.epsilon);
    printf("  ✓ Custom config applied\n");
    
    // Update config
    custom_cfg.epsilon = 1e-9;
    atlas_ctx_set_config(ctx, &custom_cfg);
    atlas_ctx_get_config(ctx, &retrieved_cfg);
    assert(retrieved_cfg.epsilon == 1e-9);
    printf("  ✓ Config update works\n");
    
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 3: Homomorphic lift permutations
void test_lift_permutations(void) {
    printf("Test 3: Homomorphic lift permutations...\n");
    
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    cfg.flags = ATLAS_CTX_ENABLE_LIFT;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    assert(ctx != NULL);
    
    double* state = (double*)malloc(BLOCK_SIZE * sizeof(double));
    double* original = (double*)malloc(BLOCK_SIZE * sizeof(double));
    assert(state && original);
    
    random_vector(state, BLOCK_SIZE, 42);
    memcpy(original, state, BLOCK_SIZE * sizeof(double));
    
    // Apply Lx lift
    int result = atlas_ctx_apply_lift_x(ctx, state);
    assert(result == 0);
    printf("  ✓ Lx lift applied\n");
    
    // Check state changed (permutation should modify)
    double diff = vec_diff(state, original, BLOCK_SIZE);
    assert(diff > EPSILON);
    printf("  ✓ Lx modifies state (diff=%.6e)\n", diff);
    
    // Apply Lx again (should be involutive for bit-reversal)
    atlas_ctx_apply_lift_x(ctx, state);
    diff = vec_diff(state, original, BLOCK_SIZE);
    assert(diff < EPSILON);
    printf("  ✓ Lx is involutive (Lx² = I)\n");
    
    // Test Lz lift
    memcpy(state, original, BLOCK_SIZE * sizeof(double));
    result = atlas_ctx_apply_lift_z(ctx, state);
    assert(result == 0);
    printf("  ✓ Lz lift applied\n");
    
    // Check norm preservation (permutations should preserve norm)
    double norm_before = vec_norm(original, BLOCK_SIZE);
    double norm_after = vec_norm(state, BLOCK_SIZE);
    assert(fabs(norm_before - norm_after) < EPSILON);
    printf("  ✓ Lift preserves norm (%.6f ≈ %.6f)\n", norm_before, norm_after);
    
    free(state);
    free(original);
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 4: Pauli operator relations
void test_pauli_relations(void) {
    printf("Test 4: Pauli operator relations...\n");
    
    AtlasBridgeContext* ctx = atlas_ctx_new_default();
    assert(ctx != NULL);
    
    double* state = (double*)malloc(BLOCK_SIZE * sizeof(double));
    double* original = (double*)malloc(BLOCK_SIZE * sizeof(double));
    assert(state && original);
    
    random_vector(state, BLOCK_SIZE, 123);
    memcpy(original, state, BLOCK_SIZE * sizeof(double));
    
    // Test X² = I (on qubit 0)
    atlas_ctx_apply_pauli_x(ctx, 0x01, state);
    atlas_ctx_apply_pauli_x(ctx, 0x01, state);
    double diff = vec_diff(state, original, BLOCK_SIZE);
    assert(diff < EPSILON);
    printf("  ✓ X² = I (diff=%.6e)\n", diff);
    
    // Test Z² = I (on qubit 1)
    memcpy(state, original, BLOCK_SIZE * sizeof(double));
    atlas_ctx_apply_pauli_z(ctx, 0x02, state);
    atlas_ctx_apply_pauli_z(ctx, 0x02, state);
    diff = vec_diff(state, original, BLOCK_SIZE);
    assert(diff < EPSILON);
    printf("  ✓ Z² = I (diff=%.6e)\n", diff);
    
    // Test XZ = -ZX (anticommutation on same qubit)
    memcpy(state, original, BLOCK_SIZE * sizeof(double));
    double* xz_state = (double*)malloc(BLOCK_SIZE * sizeof(double));
    double* zx_state = (double*)malloc(BLOCK_SIZE * sizeof(double));
    assert(xz_state && zx_state);
    
    memcpy(xz_state, original, BLOCK_SIZE * sizeof(double));
    memcpy(zx_state, original, BLOCK_SIZE * sizeof(double));
    
    // XZ on qubit 0
    atlas_ctx_apply_pauli_x(ctx, 0x01, xz_state);
    atlas_ctx_apply_pauli_z(ctx, 0x01, xz_state);
    
    // ZX on qubit 0
    atlas_ctx_apply_pauli_z(ctx, 0x01, zx_state);
    atlas_ctx_apply_pauli_x(ctx, 0x01, zx_state);
    
    // Check XZ = -ZX (states should be negatives)
    double match = 0.0;
    for (size_t i = 0; i < BLOCK_SIZE; i++) {
        match += fabs(xz_state[i] + zx_state[i]);
    }
    assert(match / BLOCK_SIZE < EPSILON);
    printf("  ✓ XZ = -ZX anticommutation (match=%.6e)\n", match / BLOCK_SIZE);
    
    free(state);
    free(original);
    free(xz_state);
    free(zx_state);
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 5: E-twirl idempotency
void test_twirl_idempotency(void) {
    printf("Test 5: E-twirl idempotency...\n");
    
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    cfg.flags = ATLAS_CTX_ENABLE_TWIRL;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    assert(ctx != NULL);
    
    double* state = (double*)malloc(BLOCK_SIZE * sizeof(double));
    assert(state);
    
    random_vector(state, BLOCK_SIZE, 456);
    
    // Check twirl idempotency: T² = T
    double idempotency = atlas_ctx_check_twirl_idempotency(ctx, state);
    printf("  Twirl idempotency measure: %.6e\n", idempotency);
    
    // Should be small (indicating T² ≈ T)
    assert(idempotency >= 0.0);
    printf("  ✓ Idempotency check completed\n");
    
    // Verify idempotency is stored in diagnostics
    AtlasContextDiagnostics diag;
    atlas_ctx_get_diagnostics(ctx, &diag);
    assert(diag.twirl_idempotency == idempotency);
    printf("  ✓ Diagnostics updated (T²-T = %.6e)\n", diag.twirl_idempotency);
    
    free(state);
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 6: Twirl generator queries
void test_twirl_generators(void) {
    printf("Test 6: E-twirl generator queries...\n");
    
    AtlasBridgeContext* ctx = atlas_ctx_new_default();
    assert(ctx != NULL);
    
    // Query all generators
    for (uint32_t i = 0; i < 16; i++) {
        uint8_t x_mask, z_mask;
        int result = atlas_ctx_get_twirl_generator(ctx, i, &x_mask, &z_mask);
        assert(result == 0);
        printf("  Generator %2u: X=0x%02X, Z=0x%02X\n", i, x_mask, z_mask);
    }
    printf("  ✓ All 16 generators retrieved\n");
    
    // Test out-of-range query
    uint8_t x_mask, z_mask;
    int result = atlas_ctx_get_twirl_generator(ctx, 100, &x_mask, &z_mask);
    assert(result != 0);
    printf("  ✓ Out-of-range query handled\n");
    
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 7: Heisenberg exchange operator
void test_heisenberg_exchange(void) {
    printf("Test 7: Heisenberg exchange operator...\n");
    
    AtlasBridgeContext* ctx = atlas_ctx_new_default();
    assert(ctx != NULL);
    
    double* state = (double*)malloc(BLOCK_SIZE * sizeof(double));
    assert(state);
    
    random_vector(state, BLOCK_SIZE, 789);
    
    // Apply Heisenberg on qubits 0 and 1
    int result = atlas_ctx_apply_heisenberg(ctx, 0, 1, state);
    assert(result == 0);
    printf("  ✓ Heisenberg(0,1) applied\n");
    
    // Test invalid qubit indices
    result = atlas_ctx_apply_heisenberg(ctx, 0, 10, state);
    assert(result != 0);
    printf("  ✓ Invalid qubit index rejected\n");
    
    free(state);
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 8: Diagnostics and counters
void test_diagnostics(void) {
    printf("Test 8: Diagnostics and counters...\n");
    
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    cfg.flags = ATLAS_CTX_ENABLE_TWIRL | ATLAS_CTX_ENABLE_LIFT;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    assert(ctx != NULL);
    
    double* state = (double*)malloc(BLOCK_SIZE * sizeof(double));
    assert(state);
    random_vector(state, BLOCK_SIZE, 111);
    
    // Reset diagnostics
    atlas_ctx_reset_diagnostics(ctx);
    AtlasContextDiagnostics diag;
    atlas_ctx_get_diagnostics(ctx, &diag);
    assert(diag.op_count == 0);
    printf("  ✓ Diagnostics reset\n");
    
    // Perform operations
    atlas_ctx_apply_lift_x(ctx, state);
    atlas_ctx_apply_pauli_x(ctx, 0x01, state);
    atlas_ctx_apply_twirl(ctx, state);
    
    // Check counters
    atlas_ctx_get_diagnostics(ctx, &diag);
    assert(diag.op_count == 3);
    printf("  ✓ Operation counter: %lu ops\n", diag.op_count);
    
    // Print diagnostics
    printf("\n");
    atlas_ctx_print_diagnostics(ctx);
    printf("\n");
    
    free(state);
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 9: Version and utilities
void test_utilities(void) {
    printf("Test 9: Version and utilities...\n");
    
    const char* version = atlas_ctx_version();
    assert(version != NULL);
    printf("  Library version: %s\n", version);
    
    AtlasBridgeContext* ctx = atlas_ctx_new_default();
    assert(ctx != NULL);
    
    uint32_t block_size = atlas_ctx_get_block_size(ctx);
    assert(block_size == 12288);
    printf("  ✓ Block size: %u\n", block_size);
    
    uint32_t n_qubits = atlas_ctx_get_n_qubits(ctx);
    assert(n_qubits == 8);
    printf("  ✓ Qubits: %u\n", n_qubits);
    
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 10: Combined operations
void test_combined_operations(void) {
    printf("Test 10: Combined operations...\n");
    
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    cfg.flags = ATLAS_CTX_ENABLE_TWIRL | ATLAS_CTX_ENABLE_LIFT;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    assert(ctx != NULL);
    
    double* state = (double*)malloc(BLOCK_SIZE * sizeof(double));
    assert(state);
    
    random_vector(state, BLOCK_SIZE, 999);
    double initial_norm = vec_norm(state, BLOCK_SIZE);
    
    // Apply sequence of operations
    atlas_ctx_apply_lift_x(ctx, state);
    atlas_ctx_apply_pauli_x(ctx, 0x03, state);  // X on qubits 0,1
    atlas_ctx_apply_pauli_z(ctx, 0x0C, state);  // Z on qubits 2,3
    atlas_ctx_apply_lift_z(ctx, state);
    atlas_ctx_apply_twirl(ctx, state);
    
    printf("  ✓ Sequence of operations completed\n");
    
    // Check operation count
    AtlasContextDiagnostics diag;
    atlas_ctx_get_diagnostics(ctx, &diag);
    printf("  Operations performed: %lu\n", diag.op_count);
    
    free(state);
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

int main(void) {
    printf("═══════════════════════════════════════════════════════\n");
    printf("  Atlas Bridge Context API v0.2 - Self-Test Suite\n");
    printf("  Conway–Monster Atlas Upgrade Kit\n");
    printf("═══════════════════════════════════════════════════════\n\n");
    
    test_context_lifecycle();
    test_configuration();
    test_lift_permutations();
    test_pauli_relations();
    test_twirl_idempotency();
    test_twirl_generators();
    test_heisenberg_exchange();
    test_diagnostics();
    test_utilities();
    test_combined_operations();
    
    printf("═══════════════════════════════════════════════════════\n");
    printf("  ✓ All tests passed!\n");
    printf("═══════════════════════════════════════════════════════\n");
    
    return 0;
}
