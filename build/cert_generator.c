#include "atlas_bridge_ctx.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char** argv) {
    const char* cert_path = argc > 1 ? argv[1] : "bridge_cert.json";
    const char* artifacts_dir = argc > 2 ? argv[2] : "atlas/artifacts";
    
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
    
    // Build paths to artifacts
    char lift_path[256];
    char p299_path[256];
    char co1_path[256];
    snprintf(lift_path, sizeof(lift_path), "%s/lift_forms.hex", artifacts_dir);
    snprintf(p299_path, sizeof(p299_path), "%s/P_299_matrix.bin", artifacts_dir);
    snprintf(co1_path, sizeof(co1_path), "%s/co1_gates.txt", artifacts_dir);
    
    // Load lift forms if available
    if (atlas_ctx_load_lift_forms(ctx, lift_path) == 0) {
        printf("Loaded lift forms from %s\n", lift_path);
    } else {
        printf("Using default lift forms\n");
    }
    
    // Try to load P_299 matrix if available
    if (atlas_ctx_load_p299_matrix(ctx, p299_path) == 0) {
        printf("Loaded exact P_299 matrix\n");
    } else {
        printf("Using P_299 fallback logic\n");
    }
    
    // Try to load Co1 gates if available
    if (atlas_ctx_load_co1_gates(ctx, co1_path) == 0) {
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
