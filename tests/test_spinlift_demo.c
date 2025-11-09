// tests/test_spinlift_demo.c
// Atlas Bridge Context API v0.2 - Spinlift Demo
// Conway–Monster Atlas Upgrade Kit
//
// Demonstrates lift-mass calculation after twirl operation

#include "../atlas_core/include/atlas_bridge_ctx.h"
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>

#define BLOCK_SIZE 12288

// Compute total mass (L1 norm) of state vector
static double compute_mass(const double* state, size_t n) {
    double mass = 0.0;
    for (size_t i = 0; i < n; i++) {
        mass += fabs(state[i]);
    }
    return mass;
}

// Compute L2 norm
static double compute_norm(const double* state, size_t n) {
    double norm = 0.0;
    for (size_t i = 0; i < n; i++) {
        norm += state[i] * state[i];
    }
    return sqrt(norm);
}

// Compute concentration (ratio of max to mean)
static double compute_concentration(const double* state, size_t n) {
    double max_val = 0.0;
    double sum = 0.0;
    
    for (size_t i = 0; i < n; i++) {
        double abs_val = fabs(state[i]);
        if (abs_val > max_val) max_val = abs_val;
        sum += abs_val;
    }
    
    double mean = sum / n;
    return (mean > 0.0) ? (max_val / mean) : 0.0;
}

// Initialize state with localized distribution (simulates physical preparation)
static void init_localized_state(double* state, size_t n) {
    // Create a Gaussian-like distribution centered around middle
    size_t center = n / 2;
    double sigma = n / 20.0;  // Width parameter
    
    for (size_t i = 0; i < n; i++) {
        double x = (double)i - center;
        state[i] = exp(-x * x / (2.0 * sigma * sigma));
    }
    
    // Normalize
    double norm = compute_norm(state, n);
    for (size_t i = 0; i < n; i++) {
        state[i] /= norm;
    }
}

int main(void) {
    printf("═══════════════════════════════════════════════════════\n");
    printf("  Atlas Bridge Context API v0.2 - Spinlift Demo\n");
    printf("  Conway–Monster Atlas Upgrade Kit\n");
    printf("═══════════════════════════════════════════════════════\n\n");
    
    printf("This demo shows the effect of E-twirl and lift operations\n");
    printf("on quantum state mass distribution.\n\n");
    
    // Create context with twirl and lift enabled
    AtlasContextConfig cfg;
    atlas_ctx_config_default(&cfg);
    cfg.flags = ATLAS_CTX_ENABLE_TWIRL | ATLAS_CTX_ENABLE_LIFT | ATLAS_CTX_VERBOSE;
    
    AtlasBridgeContext* ctx = atlas_ctx_new(&cfg);
    if (!ctx) {
        fprintf(stderr, "Failed to create context\n");
        return 1;
    }
    
    printf("Context created with:\n");
    printf("  Block size: %u\n", cfg.block_size);
    printf("  Qubits: %u\n", cfg.n_qubits);
    printf("  Twirl generators: %u\n", cfg.twirl_gens);
    printf("  Epsilon: %.2e\n\n", cfg.epsilon);
    
    // Allocate state vector
    double* state = (double*)malloc(BLOCK_SIZE * sizeof(double));
    if (!state) {
        fprintf(stderr, "Failed to allocate state vector\n");
        atlas_ctx_free(ctx);
        return 1;
    }
    
    // Initialize with localized state
    init_localized_state(state, BLOCK_SIZE);
    
    printf("─── Initial State ───────────────────────────────────────\n");
    double initial_mass = compute_mass(state, BLOCK_SIZE);
    double initial_norm = compute_norm(state, BLOCK_SIZE);
    double initial_conc = compute_concentration(state, BLOCK_SIZE);
    
    printf("  L1 mass: %.6f\n", initial_mass);
    printf("  L2 norm: %.6f\n", initial_norm);
    printf("  Concentration: %.2f\n", initial_conc);
    printf("\n");
    
    // Step 1: Apply homomorphic lift Lx
    printf("─── Step 1: Apply Lift Lx ───────────────────────────────\n");
    if (atlas_ctx_apply_lift_x(ctx, state) != 0) {
        fprintf(stderr, "Failed to apply Lx\n");
        free(state);
        atlas_ctx_free(ctx);
        return 1;
    }
    
    double lift_x_mass = compute_mass(state, BLOCK_SIZE);
    double lift_x_norm = compute_norm(state, BLOCK_SIZE);
    double lift_x_conc = compute_concentration(state, BLOCK_SIZE);
    
    printf("  L1 mass: %.6f (Δ = %+.6f)\n", lift_x_mass, lift_x_mass - initial_mass);
    printf("  L2 norm: %.6f (Δ = %+.6f)\n", lift_x_norm, lift_x_norm - initial_norm);
    printf("  Concentration: %.2f (Δ = %+.2f)\n", lift_x_conc, lift_x_conc - initial_conc);
    printf("  Note: Lx is a permutation, so norm preserved\n\n");
    
    // Step 2: Apply Pauli operations
    printf("─── Step 2: Apply Pauli X on qubits {0,1,2} ──────────────\n");
    if (atlas_ctx_apply_pauli_x(ctx, 0x07, state) != 0) {
        fprintf(stderr, "Failed to apply Pauli X\n");
        free(state);
        atlas_ctx_free(ctx);
        return 1;
    }
    
    double pauli_mass = compute_mass(state, BLOCK_SIZE);
    double pauli_norm = compute_norm(state, BLOCK_SIZE);
    double pauli_conc = compute_concentration(state, BLOCK_SIZE);
    
    printf("  L1 mass: %.6f (Δ = %+.6f)\n", pauli_mass, pauli_mass - lift_x_mass);
    printf("  L2 norm: %.6f (Δ = %+.6f)\n", pauli_norm, pauli_norm - lift_x_norm);
    printf("  Concentration: %.2f (Δ = %+.2f)\n\n", pauli_conc, pauli_conc - lift_x_conc);
    
    // Step 3: Apply E-twirl
    printf("─── Step 3: Apply E-Twirl (averaging over 16 generators) ─\n");
    if (atlas_ctx_apply_twirl(ctx, state) != 0) {
        fprintf(stderr, "Failed to apply twirl\n");
        free(state);
        atlas_ctx_free(ctx);
        return 1;
    }
    
    double twirl_mass = compute_mass(state, BLOCK_SIZE);
    double twirl_norm = compute_norm(state, BLOCK_SIZE);
    double twirl_conc = compute_concentration(state, BLOCK_SIZE);
    
    printf("  L1 mass: %.6f (Δ = %+.6f)\n", twirl_mass, twirl_mass - pauli_mass);
    printf("  L2 norm: %.6f (Δ = %+.6f)\n", twirl_norm, twirl_norm - pauli_norm);
    printf("  Concentration: %.2f (Δ = %+.2f)\n", twirl_conc, twirl_conc - pauli_conc);
    printf("  Note: Twirl spreads distribution (reduces concentration)\n\n");
    
    // Step 4: Apply lift Lz
    printf("─── Step 4: Apply Lift Lz ───────────────────────────────\n");
    if (atlas_ctx_apply_lift_z(ctx, state) != 0) {
        fprintf(stderr, "Failed to apply Lz\n");
        free(state);
        atlas_ctx_free(ctx);
        return 1;
    }
    
    double lift_z_mass = compute_mass(state, BLOCK_SIZE);
    double lift_z_norm = compute_norm(state, BLOCK_SIZE);
    double lift_z_conc = compute_concentration(state, BLOCK_SIZE);
    
    printf("  L1 mass: %.6f (Δ = %+.6f)\n", lift_z_mass, lift_z_mass - twirl_mass);
    printf("  L2 norm: %.6f (Δ = %+.6f)\n", lift_z_norm, lift_z_norm - twirl_norm);
    printf("  Concentration: %.2f (Δ = %+.2f)\n\n", lift_z_conc, lift_z_conc - twirl_conc);
    
    // Final analysis
    printf("─── Final Analysis ──────────────────────────────────────\n");
    printf("  Total mass change: %+.6f (%.2f%%)\n", 
           lift_z_mass - initial_mass,
           100.0 * (lift_z_mass - initial_mass) / initial_mass);
    printf("  Norm preservation: %.2e (should be ~0 for unitary ops)\n",
           fabs(lift_z_norm - initial_norm));
    printf("  Concentration reduction: %.2f → %.2f\n", 
           initial_conc, lift_z_conc);
    printf("\n");
    
    // Check twirl idempotency
    printf("─── Twirl Idempotency Check ─────────────────────────────\n");
    
    // Reset state
    init_localized_state(state, BLOCK_SIZE);
    
    double idempotency = atlas_ctx_check_twirl_idempotency(ctx, state);
    printf("  ||T²(v) - T(v)||₂ = %.6e\n", idempotency);
    
    if (idempotency < 1e-6) {
        printf("  ✓ Twirl is idempotent (projector is stable)\n");
    } else {
        printf("  ⚠ Twirl idempotency: %.6e (expected < 1e-6)\n", idempotency);
    }
    printf("\n");
    
    // Get final diagnostics
    AtlasContextDiagnostics diag;
    atlas_ctx_get_diagnostics(ctx, &diag);
    
    printf("─── Context Diagnostics ─────────────────────────────────\n");
    printf("  Total operations: %lu\n", diag.op_count);
    printf("  Twirl idempotency: %.6e\n", diag.twirl_idempotency);
    printf("\n");
    
    // Cleanup
    free(state);
    atlas_ctx_free(ctx);
    
    printf("═══════════════════════════════════════════════════════\n");
    printf("  ✓ Demo completed successfully!\n");
    printf("═══════════════════════════════════════════════════════\n");
    
    return 0;
}
