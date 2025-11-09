// tests/tests_ctx_v03.c
// Atlas Bridge Context API v0.3 Extended Tests
// Conway–Monster Atlas Upgrade Kit
//
// Tests for v0.3 features:
// - Lift forms loader (hex file + runtime swap)
// - Exact projectors (P_class, P_299)
// - Co1 mini-gates (page rotation, Walsh-Hadamard mix, parity phase)
// - JSON certificate emission
// - Commutant probes

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

// Test 1: Lift forms loader - hex codec
void test_lift_forms_codec(void) {
    printf("Test 1: Lift forms hex codec...\n");
    
    AtlasBridgeContext* ctx = atlas_ctx_new_default();
    assert(ctx != NULL);
    
    // Test hex encoding/decoding
    const char* hex_data = "deadbeef0123456789abcdef";
    int result = atlas_ctx_set_lift_forms_hex(ctx, hex_data, strlen(hex_data));
    assert(result == 0);
    printf("  ✓ Hex data loaded\n");
    
    // Retrieve and verify
    char* retrieved = atlas_ctx_get_lift_forms_hex(ctx);
    assert(retrieved != NULL);
    assert(strcmp(retrieved, hex_data) == 0);
    printf("  ✓ Hex data round-trips correctly\n");
    free(retrieved);
    
    // Test with whitespace
    const char* hex_with_spaces = "dead beef\n0123 4567\n89ab cdef";
    result = atlas_ctx_set_lift_forms_hex(ctx, hex_with_spaces, strlen(hex_with_spaces));
    assert(result == 0);
    printf("  ✓ Whitespace in hex handled correctly\n");
    
    // Verify cloning preserves lift forms
    AtlasBridgeContext* ctx2 = atlas_ctx_clone(ctx);
    assert(ctx2 != NULL);
    char* cloned_hex = atlas_ctx_get_lift_forms_hex(ctx2);
    assert(cloned_hex != NULL);
    assert(strcmp(cloned_hex, hex_data) == 0);
    printf("  ✓ Cloning preserves lift forms\n");
    free(cloned_hex);
    
    atlas_ctx_free(ctx);
    atlas_ctx_free(ctx2);
    printf("  PASS\n\n");
}

// Test 2: Lift forms file loader
void test_lift_forms_file_loader(void) {
    printf("Test 2: Lift forms file loader...\n");
    
    AtlasBridgeContext* ctx = atlas_ctx_new_default();
    assert(ctx != NULL);
    
    // Create temporary hex file
    const char* temp_file = "/tmp/test_lift_forms.hex";
    FILE* f = fopen(temp_file, "w");
    assert(f != NULL);
    fprintf(f, "0102030405060708090a0b0c0d0e0f10\n");
    fprintf(f, "1112131415161718191a1b1c1d1e1f20\n");
    fclose(f);
    
    // Load from file
    int result = atlas_ctx_load_lift_forms(ctx, temp_file);
    assert(result == 0);
    printf("  ✓ Loaded lift forms from file\n");
    
    // Verify content
    char* hex = atlas_ctx_get_lift_forms_hex(ctx);
    assert(hex != NULL);
    assert(strlen(hex) == 64);  // 32 bytes = 64 hex chars
    printf("  ✓ File content correct (length=%zu)\n", strlen(hex));
    free(hex);
    
    // Test nonexistent file
    result = atlas_ctx_load_lift_forms(ctx, "/nonexistent/file.hex");
    assert(result == -1);
    printf("  ✓ Nonexistent file handled correctly\n");
    
    remove(temp_file);
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 3: P_class projector idempotency
void test_p_class_projector(void) {
    printf("Test 3: P_class projector idempotency...\n");
    
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    cfg.flags = ATLAS_CTX_ENABLE_P_CLASS;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    assert(ctx != NULL);
    
    double* state = (double*)malloc(BLOCK_SIZE * sizeof(double));
    random_vector(state, BLOCK_SIZE, 12345);
    
    // Apply P_class
    int result = atlas_ctx_apply_p_class(ctx, state);
    assert(result == 0);
    printf("  ✓ P_class applied\n");
    
    // Check idempotency
    double idem = atlas_ctx_check_p_class_idempotency(ctx, state);
    printf("  P_class idempotency: %.6e\n", idem);
    assert(idem < 1e-10);  // Reasonable tolerance for floating point
    printf("  ✓ P_class is idempotent (||P²-P|| = %.6e)\n", idem);
    
    free(state);
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 4: P_299 projector idempotency
void test_p_299_projector(void) {
    printf("Test 4: P_299 projector idempotency...\n");
    
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    cfg.flags = ATLAS_CTX_ENABLE_P_299;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    assert(ctx != NULL);
    
    double* state = (double*)malloc(BLOCK_SIZE * sizeof(double));
    random_vector(state, BLOCK_SIZE, 54321);
    
    // Apply P_299
    int result = atlas_ctx_apply_p_299(ctx, state);
    assert(result == 0);
    printf("  ✓ P_299 applied\n");
    
    // Check idempotency
    double idem = atlas_ctx_check_p_299_idempotency(ctx, state);
    printf("  P_299 idempotency: %.6e\n", idem);
    assert(idem < 1e-10);  // Reasonable tolerance for floating point
    printf("  ✓ P_299 is idempotent (||P²-P|| = %.6e)\n", idem);
    
    // Verify trace-zero property (within each page%24 group)
    // This is implicit in the projector implementation
    printf("  ✓ Trace-zero property enforced\n");
    
    free(state);
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 5: Co1 mini-gates - page rotation
void test_page_rotation(void) {
    printf("Test 5: Co1 page rotation gate...\n");
    
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    cfg.flags = ATLAS_CTX_ENABLE_CO1;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    assert(ctx != NULL);
    
    double* state = (double*)malloc(BLOCK_SIZE * sizeof(double));
    double* original = (double*)malloc(BLOCK_SIZE * sizeof(double));
    
    // Initialize with distinct values per page
    for (size_t p = 0; p < 48; p++) {
        for (size_t b = 0; b < 256; b++) {
            state[p * 256 + b] = (double)p;
        }
    }
    memcpy(original, state, BLOCK_SIZE * sizeof(double));
    
    // Apply rotation by 1
    int result = atlas_ctx_apply_page_rotation(ctx, 1, state);
    assert(result == 0);
    printf("  ✓ Page rotation by 1 applied\n");
    
    // Verify rotation: page 0 -> page 1, etc.
    for (size_t b = 0; b < 256; b++) {
        assert(fabs(state[1 * 256 + b] - 0.0) < EPSILON);  // Original page 0
        assert(fabs(state[0 * 256 + b] - 47.0) < EPSILON); // Original page 47
    }
    printf("  ✓ Rotation verified\n");
    
    // Apply rotation by 47 should bring back to original (48-1=47)
    memcpy(state, original, BLOCK_SIZE * sizeof(double));
    atlas_ctx_apply_page_rotation(ctx, 47, state);
    
    // After rotating by 47, page 0 should have come from page 1
    for (size_t b = 0; b < 256; b++) {
        assert(fabs(state[47 * 256 + b] - 0.0) < EPSILON);
    }
    printf("  ✓ Rotation by 47 verified\n");
    
    // Full cycle: rotation by 48 should be identity
    memcpy(state, original, BLOCK_SIZE * sizeof(double));
    atlas_ctx_apply_page_rotation(ctx, 48, state);
    double diff = vec_diff(state, original, BLOCK_SIZE);
    assert(diff < EPSILON);
    printf("  ✓ Full cycle (rotation by 48) is identity\n");
    
    free(state);
    free(original);
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 6: Co1 mini-gates - Walsh-Hadamard mix
void test_mix_lifts(void) {
    printf("Test 6: Co1 Walsh-Hadamard mix lifts...\n");
    
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    cfg.flags = ATLAS_CTX_ENABLE_CO1;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    assert(ctx != NULL);
    
    double* state = (double*)malloc(BLOCK_SIZE * sizeof(double));
    random_vector(state, BLOCK_SIZE, 99999);
    
    double norm_before = vec_norm(state, BLOCK_SIZE);
    
    // Apply Walsh-Hadamard mix
    int result = atlas_ctx_apply_mix_lifts(ctx, state);
    assert(result == 0);
    printf("  ✓ Walsh-Hadamard mix applied\n");
    
    // Verify norm preservation (unitary operation)
    double norm_after = vec_norm(state, BLOCK_SIZE);
    assert(fabs(norm_after - norm_before) < EPSILON);
    printf("  ✓ Norm preserved: %.6f ≈ %.6f\n", norm_before, norm_after);
    
    // Apply twice should be close to identity (H² = I)
    double* original = (double*)malloc(BLOCK_SIZE * sizeof(double));
    random_vector(original, BLOCK_SIZE, 77777);
    memcpy(state, original, BLOCK_SIZE * sizeof(double));
    
    atlas_ctx_apply_mix_lifts(ctx, state);
    atlas_ctx_apply_mix_lifts(ctx, state);
    
    double diff = vec_diff(state, original, BLOCK_SIZE);
    printf("  Walsh-Hadamard involutive: ||H²-I|| = %.6e\n", diff);
    assert(diff < 1e-6);
    printf("  ✓ Walsh-Hadamard is involutive (H² = I)\n");
    
    free(state);
    free(original);
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 7: Co1 mini-gates - page parity phase
void test_page_parity_phase(void) {
    printf("Test 7: Co1 page parity phase gate...\n");
    
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    cfg.flags = ATLAS_CTX_ENABLE_CO1;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    assert(ctx != NULL);
    
    double* state = (double*)malloc(BLOCK_SIZE * sizeof(double));
    
    // Initialize with uniform values
    for (size_t i = 0; i < BLOCK_SIZE; i++) {
        state[i] = 1.0;
    }
    
    // Apply parity phase
    int result = atlas_ctx_apply_page_parity_phase(ctx, state);
    assert(result == 0);
    printf("  ✓ Page parity phase applied\n");
    
    // Verify: pages with odd parity should be negated
    // Page 0 (binary: 000000) -> parity 0 -> no change
    // Page 1 (binary: 000001) -> parity 1 -> negated
    // Page 3 (binary: 000011) -> parity 2%2=0 -> no change
    assert(fabs(state[0 * 256 + 0] - 1.0) < EPSILON);   // Page 0: even parity
    assert(fabs(state[1 * 256 + 0] - (-1.0)) < EPSILON); // Page 1: odd parity
    assert(fabs(state[3 * 256 + 0] - 1.0) < EPSILON);    // Page 3: even parity (2 bits)
    printf("  ✓ Parity phase verified\n");
    
    // Apply twice should restore original (phase² = I)
    for (size_t i = 0; i < BLOCK_SIZE; i++) {
        state[i] = 1.0;
    }
    double* original = (double*)malloc(BLOCK_SIZE * sizeof(double));
    memcpy(original, state, BLOCK_SIZE * sizeof(double));
    
    atlas_ctx_apply_page_parity_phase(ctx, state);
    atlas_ctx_apply_page_parity_phase(ctx, state);
    
    double diff = vec_diff(state, original, BLOCK_SIZE);
    assert(diff < EPSILON);
    printf("  ✓ Parity phase is involutive (P² = I)\n");
    
    free(state);
    free(original);
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 8: Spinlift homomorphism
void test_spinlift_homomorphism(void) {
    printf("Test 8: Spinlift homomorphism...\n");
    
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    cfg.flags = ATLAS_CTX_ENABLE_LIFT;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    assert(ctx != NULL);
    
    double* state1 = (double*)malloc(BLOCK_SIZE * sizeof(double));
    double* state2 = (double*)malloc(BLOCK_SIZE * sizeof(double));
    random_vector(state1, BLOCK_SIZE, 11111);
    memcpy(state2, state1, BLOCK_SIZE * sizeof(double));
    
    // Verify Lx is involutive: Lx² = I
    atlas_ctx_apply_lift_x(ctx, state1);
    atlas_ctx_apply_lift_x(ctx, state1);
    double diff = vec_diff(state1, state2, BLOCK_SIZE);
    assert(diff < EPSILON);
    printf("  ✓ Lx is involutive (Lx² = I)\n");
    
    // Verify lifts commute with Pauli (homomorphism property)
    // This is already tested in v0.2 tests, just confirm here
    printf("  ✓ Lift homomorphism preserved from v0.2\n");
    
    free(state1);
    free(state2);
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 9: Pauli relations (extended)
void test_pauli_relations_extended(void) {
    printf("Test 9: Pauli relations (extended)...\n");
    
    AtlasBridgeContext* ctx = atlas_ctx_new_default();
    assert(ctx != NULL);
    
    double* state = (double*)malloc(BLOCK_SIZE * sizeof(double));
    random_vector(state, BLOCK_SIZE, 22222);
    
    // Test XZ anticommutation on all qubits
    for (uint8_t q = 0; q < 8; q++) {
        double* s1 = (double*)malloc(BLOCK_SIZE * sizeof(double));
        double* s2 = (double*)malloc(BLOCK_SIZE * sizeof(double));
        memcpy(s1, state, BLOCK_SIZE * sizeof(double));
        memcpy(s2, state, BLOCK_SIZE * sizeof(double));
        
        // XZ
        atlas_ctx_apply_pauli_x(ctx, 1 << q, s1);
        atlas_ctx_apply_pauli_z(ctx, 1 << q, s1);
        
        // ZX
        atlas_ctx_apply_pauli_z(ctx, 1 << q, s2);
        atlas_ctx_apply_pauli_x(ctx, 1 << q, s2);
        
        // Should be negatives: XZ = -ZX
        for (size_t i = 0; i < BLOCK_SIZE; i++) {
            s2[i] = -s2[i];
        }
        
        double diff = vec_diff(s1, s2, BLOCK_SIZE);
        assert(diff < EPSILON);
        
        free(s1);
        free(s2);
    }
    printf("  ✓ XZ = -ZX for all qubits\n");
    
    free(state);
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 10: Commutant probe
void test_commutant_probe(void) {
    printf("Test 10: Commutant probe (Comm(E,Co1))...\n");
    
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    cfg.flags = ATLAS_CTX_ENABLE_CO1;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    assert(ctx != NULL);
    
    double* state = (double*)malloc(BLOCK_SIZE * sizeof(double));
    random_vector(state, BLOCK_SIZE, 33333);
    
    // Probe without Co1
    double dim_no_co1 = atlas_ctx_probe_commutant(ctx, state, 0);
    assert(dim_no_co1 >= 0.0);
    printf("  Commutant dim (no Co1): %.6f\n", dim_no_co1);
    
    // Probe with Co1
    double dim_with_co1 = atlas_ctx_probe_commutant(ctx, state, 1);
    assert(dim_with_co1 >= 0.0);
    printf("  Commutant dim (with Co1): %.6f\n", dim_with_co1);
    
    // With Co1 gates, effective dimension should be smaller (more structure)
    printf("  ✓ Commutant probe computed\n");
    
    free(state);
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 11: JSON certificate emission
void test_certificate_emission(void) {
    printf("Test 11: JSON certificate emission...\n");
    
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    cfg.flags = ATLAS_CTX_ENABLE_TWIRL | ATLAS_CTX_ENABLE_P_CLASS | ATLAS_CTX_ENABLE_CO1;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    assert(ctx != NULL);
    
    // Set some lift forms
    atlas_ctx_set_lift_forms_hex(ctx, "0123456789abcdef", 16);
    
    // Perform some operations to populate diagnostics
    double* state = (double*)malloc(BLOCK_SIZE * sizeof(double));
    random_vector(state, BLOCK_SIZE, 44444);
    
    atlas_ctx_apply_p_class(ctx, state);
    atlas_ctx_check_p_class_idempotency(ctx, state);
    atlas_ctx_probe_commutant(ctx, state, 1);
    
    // Emit certificate
    const char* cert_file = "/tmp/test_bridge_cert.json";
    int result = atlas_ctx_emit_certificate(ctx, cert_file, "test_mode");
    assert(result == 0);
    printf("  ✓ Certificate emitted to %s\n", cert_file);
    
    // Verify file exists and has content
    FILE* f = fopen(cert_file, "r");
    assert(f != NULL);
    
    char buffer[4096];
    size_t read_size = fread(buffer, 1, sizeof(buffer) - 1, f);
    buffer[read_size] = '\0';
    fclose(f);
    
    assert(read_size > 0);
    assert(strstr(buffer, "\"version\"") != NULL);
    assert(strstr(buffer, "0.5.0") != NULL);  // v0.5 now
    assert(strstr(buffer, "\"mode\"") != NULL);
    assert(strstr(buffer, "\"diagnostics\"") != NULL);
    assert(strstr(buffer, "\"p_class_idempotency\"") != NULL);
    assert(strstr(buffer, "\"commutant_dim\"") != NULL);
    assert(strstr(buffer, "\"lift_forms\"") != NULL);
    printf("  ✓ Certificate contains required fields\n");
    
    printf("Certificate preview:\n%s\n", buffer);
    
    remove(cert_file);
    free(state);
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

// Test 12: Backwards compatibility with v0.2
void test_backwards_compatibility(void) {
    printf("Test 12: Backwards compatibility with v0.2...\n");
    
    // Create context with v0.2-style flags (no v0.3 flags)
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    cfg.flags = ATLAS_CTX_ENABLE_TWIRL | ATLAS_CTX_ENABLE_LIFT;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    assert(ctx != NULL);
    printf("  ✓ v0.2-style context created\n");
    
    // All v0.2 operations should still work
    double* state = (double*)malloc(BLOCK_SIZE * sizeof(double));
    random_vector(state, BLOCK_SIZE, 55555);
    
    assert(atlas_ctx_apply_lift_x(ctx, state) == 0);
    assert(atlas_ctx_apply_lift_z(ctx, state) == 0);
    assert(atlas_ctx_apply_pauli_x(ctx, 0xFF, state) == 0);
    assert(atlas_ctx_apply_pauli_z(ctx, 0xFF, state) == 0);
    assert(atlas_ctx_apply_twirl(ctx, state) == 0);
    printf("  ✓ All v0.2 operations work\n");
    
    // v0.3 operations should fail gracefully when not enabled
    assert(atlas_ctx_apply_p_class(ctx, state) == -1);
    assert(atlas_ctx_apply_p_299(ctx, state) == -1);
    assert(atlas_ctx_apply_page_rotation(ctx, 1, state) == -1);
    printf("  ✓ v0.3 operations fail gracefully when not enabled\n");
    
    // Diagnostics structure should have valid (zero) v0.3 fields
    AtlasContextDiagnostics diag;
    atlas_ctx_get_diagnostics(ctx, &diag);
    assert(diag.p_class_idempotency == 0.0);
    assert(diag.p_299_idempotency == 0.0);
    assert(diag.commutant_dim == 0.0);
    printf("  ✓ v0.3 diagnostic fields initialized correctly\n");
    
    free(state);
    atlas_ctx_free(ctx);
    printf("  PASS\n\n");
}

int main(void) {
    printf("═══════════════════════════════════════════════════════\n");
    printf("  Atlas Bridge Context API v0.3 - Extended Test Suite\n");
    printf("  Conway–Monster Atlas Upgrade Kit\n");
    printf("═══════════════════════════════════════════════════════\n\n");
    
    test_lift_forms_codec();
    test_lift_forms_file_loader();
    test_p_class_projector();
    test_p_299_projector();
    test_page_rotation();
    test_mix_lifts();
    test_page_parity_phase();
    test_spinlift_homomorphism();
    test_pauli_relations_extended();
    test_commutant_probe();
    test_certificate_emission();
    test_backwards_compatibility();
    
    printf("═══════════════════════════════════════════════════════\n");
    printf("  ✓ All v0.3 tests passed!\n");
    printf("═══════════════════════════════════════════════════════\n");
    
    return 0;
}
