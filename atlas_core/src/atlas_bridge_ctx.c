// atlas_core/src/atlas_bridge_ctx.c
// Atlas Bridge Context API v0.2 Implementation
// Conway–Monster Atlas Upgrade Kit

#include "../include/atlas_bridge_ctx.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <math.h>

// Internal context structure
struct AtlasBridgeContext {
    AtlasContextConfig config;
    AtlasContextDiagnostics diag;
    
    // Pre-computed E-twirl generators (x_mask, z_mask pairs)
    uint8_t* twirl_x_masks;
    uint8_t* twirl_z_masks;
    
    // Working buffers
    double* temp_buffer;
    double* twirl_accumulator;
    
    // Internal state
    int initialized;
};

// Library version
static const char* VERSION = "0.2.0";

// Default E-twirl generators (16 generators for 8-qubit Pauli group)
// These are carefully chosen to cover representative directions in the Pauli group
static const uint8_t DEFAULT_TWIRL_X[16] = {
    0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40,
    0x03, 0x05, 0x0A, 0x11, 0x22, 0x44, 0x88, 0xFF
};

static const uint8_t DEFAULT_TWIRL_Z[16] = {
    0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40,
    0x0C, 0x14, 0x28, 0x50, 0xA0, 0x41, 0x82, 0xFF
};

// ============================================================================
// Helper Functions
// ============================================================================

// Apply single-qubit Pauli X to state vector
static void apply_pauli_x_single(double* state, size_t n, uint8_t qubit) {
    // X flips the qubit bit in the computational basis
    // For 8 qubits, state has 256 entries indexed by byte value
    // This is a reduced-rank operation on byte axis
    if (qubit >= 8) return;
    
    uint8_t mask = 1 << qubit;
    for (size_t page = 0; page < (n / 256); page++) {
        size_t base = page * 256;
        for (size_t byte = 0; byte < 256; byte++) {
            size_t flipped_byte = byte ^ mask;
            if (byte < flipped_byte) {
                // Swap entries
                double temp = state[base + byte];
                state[base + byte] = state[base + flipped_byte];
                state[base + flipped_byte] = temp;
            }
        }
    }
}

// Apply single-qubit Pauli Z to state vector
static void apply_pauli_z_single(double* state, size_t n, uint8_t qubit) {
    // Z applies phase (-1) when qubit is |1⟩
    if (qubit >= 8) return;
    
    uint8_t mask = 1 << qubit;
    for (size_t i = 0; i < n; i++) {
        uint8_t byte = i % 256;
        if (byte & mask) {
            state[i] = -state[i];
        }
    }
}

// Compute L2 norm of vector
static double vec_norm(const double* v, size_t n) {
    double sum = 0.0;
    for (size_t i = 0; i < n; i++) {
        sum += v[i] * v[i];
    }
    return sqrt(sum);
}

// Compute L2 distance between vectors
static double vec_distance(const double* a, const double* b, size_t n) {
    double sum = 0.0;
    for (size_t i = 0; i < n; i++) {
        double diff = a[i] - b[i];
        sum += diff * diff;
    }
    return sqrt(sum);
}

// Copy vector
static void vec_copy(double* dst, const double* src, size_t n) {
    memcpy(dst, src, n * sizeof(double));
}

// Zero vector
static void vec_zero(double* v, size_t n) {
    memset(v, 0, n * sizeof(double));
}

// Scale vector
static void vec_scale(double* v, size_t n, double alpha) {
    for (size_t i = 0; i < n; i++) {
        v[i] *= alpha;
    }
}

// Add vector: dst += alpha * src
static void vec_axpy(double* dst, const double* src, size_t n, double alpha) {
    for (size_t i = 0; i < n; i++) {
        dst[i] += alpha * src[i];
    }
}

// ============================================================================
// Context Lifecycle
// ============================================================================

void atlas_ctx_config_default(AtlasContextConfig* config) {
    if (!config) return;
    
    config->flags = ATLAS_CTX_DEFAULT;
    config->block_size = 12288;  // 48 pages × 256 bytes
    config->n_qubits = 8;        // 8-qubit in-block operations
    config->twirl_gens = 16;     // 16 E-twirl generators
    config->epsilon = 1e-10;     // Tolerance for idempotency
}

AtlasBridgeContext* atlas_ctx_new_default(void) {
    AtlasContextConfig config;
    atlas_ctx_config_default(&config);
    return atlas_ctx_new(&config);
}

AtlasBridgeContext* atlas_ctx_new(const AtlasContextConfig* config) {
    AtlasBridgeContext* ctx = (AtlasBridgeContext*)calloc(1, sizeof(AtlasBridgeContext));
    if (!ctx) return NULL;
    
    // Set configuration
    if (config) {
        ctx->config = *config;
    } else {
        atlas_ctx_config_default(&ctx->config);
    }
    
    // Allocate twirl generator storage
    ctx->twirl_x_masks = (uint8_t*)malloc(ctx->config.twirl_gens * sizeof(uint8_t));
    ctx->twirl_z_masks = (uint8_t*)malloc(ctx->config.twirl_gens * sizeof(uint8_t));
    
    if (!ctx->twirl_x_masks || !ctx->twirl_z_masks) {
        atlas_ctx_free(ctx);
        return NULL;
    }
    
    // Initialize with default generators
    size_t n_copy = ctx->config.twirl_gens < 16 ? ctx->config.twirl_gens : 16;
    memcpy(ctx->twirl_x_masks, DEFAULT_TWIRL_X, n_copy);
    memcpy(ctx->twirl_z_masks, DEFAULT_TWIRL_Z, n_copy);
    
    // Allocate working buffers
    ctx->temp_buffer = (double*)malloc(ctx->config.block_size * sizeof(double));
    ctx->twirl_accumulator = (double*)malloc(ctx->config.block_size * sizeof(double));
    
    if (!ctx->temp_buffer || !ctx->twirl_accumulator) {
        atlas_ctx_free(ctx);
        return NULL;
    }
    
    // Initialize diagnostics
    memset(&ctx->diag, 0, sizeof(AtlasContextDiagnostics));
    
    ctx->initialized = 1;
    return ctx;
}

AtlasBridgeContext* atlas_ctx_clone(const AtlasBridgeContext* ctx) {
    if (!ctx || !ctx->initialized) return NULL;
    
    AtlasBridgeContext* new_ctx = atlas_ctx_new(&ctx->config);
    if (!new_ctx) return NULL;
    
    // Copy twirl generators
    memcpy(new_ctx->twirl_x_masks, ctx->twirl_x_masks, 
           ctx->config.twirl_gens * sizeof(uint8_t));
    memcpy(new_ctx->twirl_z_masks, ctx->twirl_z_masks,
           ctx->config.twirl_gens * sizeof(uint8_t));
    
    // Copy diagnostics
    new_ctx->diag = ctx->diag;
    
    return new_ctx;
}

void atlas_ctx_free(AtlasBridgeContext* ctx) {
    if (!ctx) return;
    
    free(ctx->twirl_x_masks);
    free(ctx->twirl_z_masks);
    free(ctx->temp_buffer);
    free(ctx->twirl_accumulator);
    free(ctx);
}

// ============================================================================
// Configuration
// ============================================================================

int atlas_ctx_get_config(const AtlasBridgeContext* ctx, AtlasContextConfig* config) {
    if (!ctx || !ctx->initialized || !config) return -1;
    
    *config = ctx->config;
    return 0;
}

int atlas_ctx_set_config(AtlasBridgeContext* ctx, const AtlasContextConfig* config) {
    if (!ctx || !ctx->initialized || !config) return -1;
    
    // Only allow updating flags and epsilon after creation
    // block_size, n_qubits, and twirl_gens require reallocation
    ctx->config.flags = config->flags;
    ctx->config.epsilon = config->epsilon;
    
    return 0;
}

// ============================================================================
// Homomorphic Lift Permutations
// ============================================================================

int atlas_ctx_apply_lift_x(AtlasBridgeContext* ctx, double* state) {
    if (!ctx || !ctx->initialized || !state) return -1;
    
    // Homomorphic lift via linear form Lx
    // This permutes the byte axis in a way that commutes with Pauli X operations
    // Implementation: bit-reversal permutation on byte indices
    
    size_t n_pages = ctx->config.block_size / 256;
    
    for (size_t page = 0; page < n_pages; page++) {
        size_t base = page * 256;
        
        // Bit-reversal permutation (8-bit)
        for (size_t byte = 0; byte < 256; byte++) {
            // Compute bit-reversed index
            uint8_t rev = 0;
            uint8_t b = (uint8_t)byte;
            for (int i = 0; i < 8; i++) {
                rev = (rev << 1) | (b & 1);
                b >>= 1;
            }
            
            if (byte < rev) {
                double temp = state[base + byte];
                state[base + byte] = state[base + rev];
                state[base + rev] = temp;
            }
        }
    }
    
    ctx->diag.op_count++;
    return 0;
}

int atlas_ctx_apply_lift_z(AtlasBridgeContext* ctx, double* state) {
    if (!ctx || !ctx->initialized || !state) return -1;
    
    // Homomorphic lift via linear form Lz
    // This permutes in a way that commutes with Pauli Z operations
    // Implementation: Gray code permutation on byte indices
    
    size_t n_pages = ctx->config.block_size / 256;
    
    vec_copy(ctx->temp_buffer, state, ctx->config.block_size);
    
    for (size_t page = 0; page < n_pages; page++) {
        size_t base = page * 256;
        
        // Gray code permutation
        for (size_t byte = 0; byte < 256; byte++) {
            uint8_t gray = byte ^ (byte >> 1);
            state[base + gray] = ctx->temp_buffer[base + byte];
        }
    }
    
    ctx->diag.op_count++;
    return 0;
}

// ============================================================================
// In-Block Pauli/Heisenberg Action
// ============================================================================

int atlas_ctx_apply_pauli_x(AtlasBridgeContext* ctx, uint8_t qubit_mask, double* state) {
    if (!ctx || !ctx->initialized || !state) return -1;
    
    // Apply Pauli X on all qubits indicated by mask
    for (uint8_t q = 0; q < ctx->config.n_qubits; q++) {
        if (qubit_mask & (1 << q)) {
            apply_pauli_x_single(state, ctx->config.block_size, q);
        }
    }
    
    ctx->diag.op_count++;
    return 0;
}

int atlas_ctx_apply_pauli_z(AtlasBridgeContext* ctx, uint8_t qubit_mask, double* state) {
    if (!ctx || !ctx->initialized || !state) return -1;
    
    // Apply Pauli Z on all qubits indicated by mask
    for (uint8_t q = 0; q < ctx->config.n_qubits; q++) {
        if (qubit_mask & (1 << q)) {
            apply_pauli_z_single(state, ctx->config.block_size, q);
        }
    }
    
    ctx->diag.op_count++;
    return 0;
}

int atlas_ctx_apply_heisenberg(AtlasBridgeContext* ctx, uint8_t q1, uint8_t q2, double* state) {
    if (!ctx || !ctx->initialized || !state) return -1;
    if (q1 >= ctx->config.n_qubits || q2 >= ctx->config.n_qubits) return -1;
    
    // Heisenberg exchange: σ_i · σ_j = X_i X_j + Y_i Y_j + Z_i Z_j
    // This is implemented as a combination of Pauli operations
    
    // Save original state
    vec_copy(ctx->temp_buffer, state, ctx->config.block_size);
    
    // XX term
    apply_pauli_x_single(state, ctx->config.block_size, q1);
    apply_pauli_x_single(state, ctx->config.block_size, q2);
    
    // YY term = -X_i Z_i X_j Z_j (with proper phase)
    apply_pauli_z_single(ctx->temp_buffer, ctx->config.block_size, q1);
    apply_pauli_x_single(ctx->temp_buffer, ctx->config.block_size, q1);
    apply_pauli_z_single(ctx->temp_buffer, ctx->config.block_size, q2);
    apply_pauli_x_single(ctx->temp_buffer, ctx->config.block_size, q2);
    vec_axpy(state, ctx->temp_buffer, ctx->config.block_size, 1.0);
    
    // ZZ term
    vec_copy(ctx->temp_buffer, state, ctx->config.block_size);
    for (size_t i = 0; i < ctx->config.block_size; i++) {
        ctx->temp_buffer[i] = state[i];
    }
    apply_pauli_z_single(ctx->temp_buffer, ctx->config.block_size, q1);
    apply_pauli_z_single(ctx->temp_buffer, ctx->config.block_size, q2);
    vec_axpy(state, ctx->temp_buffer, ctx->config.block_size, 1.0);
    
    ctx->diag.op_count++;
    return 0;
}

// ============================================================================
// E-Twirl Group Action
// ============================================================================

int atlas_ctx_apply_twirl(AtlasBridgeContext* ctx, double* state) {
    if (!ctx || !ctx->initialized || !state) return -1;
    if (!(ctx->config.flags & ATLAS_CTX_ENABLE_TWIRL)) return -1;
    
    // Average over all E-twirl generators
    vec_zero(ctx->twirl_accumulator, ctx->config.block_size);
    
    for (uint32_t g = 0; g < ctx->config.twirl_gens; g++) {
        // Copy state to temp buffer
        vec_copy(ctx->temp_buffer, state, ctx->config.block_size);
        
        // Apply generator: X then Z
        // Use internal functions to avoid incrementing op_count multiple times
        uint8_t x_mask = ctx->twirl_x_masks[g];
        uint8_t z_mask = ctx->twirl_z_masks[g];
        
        if (x_mask) {
            for (uint8_t q = 0; q < ctx->config.n_qubits; q++) {
                if (x_mask & (1 << q)) {
                    apply_pauli_x_single(ctx->temp_buffer, ctx->config.block_size, q);
                }
            }
        }
        if (z_mask) {
            for (uint8_t q = 0; q < ctx->config.n_qubits; q++) {
                if (z_mask & (1 << q)) {
                    apply_pauli_z_single(ctx->temp_buffer, ctx->config.block_size, q);
                }
            }
        }
        
        // Accumulate
        vec_axpy(ctx->twirl_accumulator, ctx->temp_buffer, 
                 ctx->config.block_size, 1.0);
    }
    
    // Average
    vec_scale(ctx->twirl_accumulator, ctx->config.block_size, 
              1.0 / ctx->config.twirl_gens);
    
    // Copy result back
    vec_copy(state, ctx->twirl_accumulator, ctx->config.block_size);
    
    ctx->diag.op_count++;
    return 0;
}

double atlas_ctx_check_twirl_idempotency(AtlasBridgeContext* ctx, const double* state) {
    if (!ctx || !ctx->initialized || !state) return -1.0;
    
    // Copy state
    vec_copy(ctx->temp_buffer, state, ctx->config.block_size);
    vec_copy(ctx->twirl_accumulator, state, ctx->config.block_size);
    
    // Apply twirl once
    atlas_ctx_apply_twirl(ctx, ctx->temp_buffer);
    
    // Apply twirl twice
    atlas_ctx_apply_twirl(ctx, ctx->twirl_accumulator);
    atlas_ctx_apply_twirl(ctx, ctx->twirl_accumulator);
    
    // Compute difference
    double diff = vec_distance(ctx->temp_buffer, ctx->twirl_accumulator, 
                               ctx->config.block_size);
    
    ctx->diag.twirl_idempotency = diff;
    return diff;
}

int atlas_ctx_get_twirl_generator(const AtlasBridgeContext* ctx, uint32_t gen_idx,
                                   uint8_t* x_mask, uint8_t* z_mask) {
    if (!ctx || !ctx->initialized) return -1;
    if (gen_idx >= ctx->config.twirl_gens) return -1;
    
    if (x_mask) *x_mask = ctx->twirl_x_masks[gen_idx];
    if (z_mask) *z_mask = ctx->twirl_z_masks[gen_idx];
    
    return 0;
}

// ============================================================================
// Diagnostics
// ============================================================================

int atlas_ctx_get_diagnostics(const AtlasBridgeContext* ctx, AtlasContextDiagnostics* diag) {
    if (!ctx || !ctx->initialized || !diag) return -1;
    
    *diag = ctx->diag;
    return 0;
}

void atlas_ctx_reset_diagnostics(AtlasBridgeContext* ctx) {
    if (!ctx || !ctx->initialized) return;
    
    memset(&ctx->diag, 0, sizeof(AtlasContextDiagnostics));
}

int atlas_ctx_validate(const AtlasBridgeContext* ctx) {
    if (!ctx) return -1;
    if (!ctx->initialized) return -1;
    if (!ctx->twirl_x_masks || !ctx->twirl_z_masks) return -1;
    if (!ctx->temp_buffer || !ctx->twirl_accumulator) return -1;
    if (ctx->config.block_size == 0) return -1;
    if (ctx->config.n_qubits == 0 || ctx->config.n_qubits > 8) return -1;
    if (ctx->config.twirl_gens == 0) return -1;
    
    return 0;
}

void atlas_ctx_print_diagnostics(const AtlasBridgeContext* ctx) {
    if (!ctx || !ctx->initialized) {
        printf("Invalid context\n");
        return;
    }
    
    printf("=== Atlas Bridge Context Diagnostics ===\n");
    printf("Version: %s\n", VERSION);
    printf("Block size: %u\n", ctx->config.block_size);
    printf("Qubits: %u\n", ctx->config.n_qubits);
    printf("Twirl generators: %u\n", ctx->config.twirl_gens);
    printf("Operation count: %lu\n", ctx->diag.op_count);
    printf("Twirl idempotency: %.6e\n", ctx->diag.twirl_idempotency);
    printf("Lift mass: %.6f\n", ctx->diag.lift_mass);
    printf("Last residual: %.6e\n", ctx->diag.last_residual);
}

// ============================================================================
// Utility Functions
// ============================================================================

const char* atlas_ctx_version(void) {
    return VERSION;
}

uint32_t atlas_ctx_get_block_size(const AtlasBridgeContext* ctx) {
    if (!ctx || !ctx->initialized) return 0;
    return ctx->config.block_size;
}

uint32_t atlas_ctx_get_n_qubits(const AtlasBridgeContext* ctx) {
    if (!ctx || !ctx->initialized) return 0;
    return ctx->config.n_qubits;
}
