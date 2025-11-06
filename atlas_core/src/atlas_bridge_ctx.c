// atlas_core/src/atlas_bridge_ctx.c
// Atlas Bridge Context API v0.3 Implementation
// Conway–Monster Atlas Upgrade Kit

#include "../include/atlas_bridge_ctx.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <math.h>
#include <time.h>

// Internal context structure
struct AtlasBridgeContext {
    AtlasContextConfig config;
    AtlasContextDiagnostics diag;
    
    // Pre-computed E-twirl generators (x_mask, z_mask pairs)
    uint8_t* twirl_x_masks;
    uint8_t* twirl_z_masks;
    
    // Lift forms storage (v0.3)
    uint8_t* lift_forms_data;
    size_t lift_forms_len;
    
    // Working buffers
    double* temp_buffer;
    double* twirl_accumulator;
    double* proj_buffer;  // v0.3: for projector operations
    
    // Internal state
    int initialized;
};

// Library version
static const char* VERSION = "0.3.0";

// Constants
#define CERT_LIFT_FORMS_HEX_LIMIT 128  // Max bytes of lift forms to include in certificate

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
    ctx->proj_buffer = (double*)malloc(ctx->config.block_size * sizeof(double));  // v0.3
    
    if (!ctx->temp_buffer || !ctx->twirl_accumulator || !ctx->proj_buffer) {
        atlas_ctx_free(ctx);
        return NULL;
    }
    
    // Initialize lift forms storage (v0.3)
    ctx->lift_forms_data = NULL;
    ctx->lift_forms_len = 0;
    
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
    
    // Copy lift forms (v0.3)
    if (ctx->lift_forms_data && ctx->lift_forms_len > 0) {
        new_ctx->lift_forms_data = (uint8_t*)malloc(ctx->lift_forms_len);
        if (new_ctx->lift_forms_data) {
            memcpy(new_ctx->lift_forms_data, ctx->lift_forms_data, ctx->lift_forms_len);
            new_ctx->lift_forms_len = ctx->lift_forms_len;
        }
    }
    
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
    free(ctx->proj_buffer);  // v0.3
    free(ctx->lift_forms_data);  // v0.3
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
    
    // Save original state for all terms
    vec_copy(ctx->twirl_accumulator, state, ctx->config.block_size);
    
    // Initialize result to zero
    vec_zero(state, ctx->config.block_size);
    
    // XX term: apply X_i X_j to original state
    vec_copy(ctx->temp_buffer, ctx->twirl_accumulator, ctx->config.block_size);
    apply_pauli_x_single(ctx->temp_buffer, ctx->config.block_size, q1);
    apply_pauli_x_single(ctx->temp_buffer, ctx->config.block_size, q2);
    vec_axpy(state, ctx->temp_buffer, ctx->config.block_size, 1.0);
    
    // YY term: apply Y_i Y_j = (iX_i Z_i)(iX_j Z_j) = -X_i Z_i X_j Z_j to original state
    vec_copy(ctx->temp_buffer, ctx->twirl_accumulator, ctx->config.block_size);
    apply_pauli_x_single(ctx->temp_buffer, ctx->config.block_size, q1);
    apply_pauli_z_single(ctx->temp_buffer, ctx->config.block_size, q1);
    apply_pauli_x_single(ctx->temp_buffer, ctx->config.block_size, q2);
    apply_pauli_z_single(ctx->temp_buffer, ctx->config.block_size, q2);
    vec_axpy(state, ctx->temp_buffer, ctx->config.block_size, 1.0);
    
    // ZZ term: apply Z_i Z_j to original state
    vec_copy(ctx->temp_buffer, ctx->twirl_accumulator, ctx->config.block_size);
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
    if (!ctx->temp_buffer || !ctx->twirl_accumulator || !ctx->proj_buffer) return -1;  // v0.3
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
    printf("P_class idempotency: %.6e\n", ctx->diag.p_class_idempotency);  // v0.3
    printf("P_299 idempotency: %.6e\n", ctx->diag.p_299_idempotency);      // v0.3
    printf("Lift mass: %.6f\n", ctx->diag.lift_mass);
    printf("Last residual: %.6e\n", ctx->diag.last_residual);
    printf("Commutant dim: %.6e\n", ctx->diag.commutant_dim);              // v0.3
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

// ============================================================================
// Lift Forms Loader (v0.3)
// ============================================================================

// Helper: Convert hex char to nibble
static int hex_char_to_nibble(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

// Helper: Convert nibble to hex char
static char nibble_to_hex_char(uint8_t n) {
    return (n < 10) ? ('0' + n) : ('a' + n - 10);
}

int atlas_ctx_load_lift_forms(AtlasBridgeContext* ctx, const char* filepath) {
    if (!ctx || !ctx->initialized || !filepath) return -1;
    
    FILE* f = fopen(filepath, "r");
    if (!f) return -1;
    
    // Read file into buffer
    fseek(f, 0, SEEK_END);
    long file_size = ftell(f);
    fseek(f, 0, SEEK_SET);
    
    if (file_size <= 0 || file_size > 1024*1024) {  // Max 1MB
        fclose(f);
        return -1;
    }
    
    char* hex_buffer = (char*)malloc(file_size + 1);
    if (!hex_buffer) {
        fclose(f);
        return -1;
    }
    
    size_t read_size = fread(hex_buffer, 1, file_size, f);
    fclose(f);
    hex_buffer[read_size] = '\0';
    
    int result = atlas_ctx_set_lift_forms_hex(ctx, hex_buffer, read_size);
    free(hex_buffer);
    
    return result;
}

// Helper: check if character is whitespace
static int is_whitespace(char c) {
    return c == ' ' || c == '\n' || c == '\r' || c == '\t';
}

int atlas_ctx_set_lift_forms_hex(AtlasBridgeContext* ctx, const char* hex_data, size_t len) {
    if (!ctx || !ctx->initialized || !hex_data) return -1;
    
    // Strip whitespace and newlines
    size_t hex_len = 0;
    for (size_t i = 0; i < len; i++) {
        if (!is_whitespace(hex_data[i])) {
            hex_len++;
        }
    }
    
    if (hex_len == 0 || hex_len % 2 != 0) return -1;
    
    size_t data_len = hex_len / 2;
    uint8_t* data = (uint8_t*)malloc(data_len);
    if (!data) return -1;
    
    // Convert hex to bytes
    size_t pos = 0;
    for (size_t i = 0; i < len && pos < data_len; ) {
        // Skip whitespace
        if (is_whitespace(hex_data[i])) {
            i++;
            continue;
        }
        
        int high = hex_char_to_nibble(hex_data[i]);
        if (high < 0) {
            free(data);
            return -1;
        }
        i++;
        
        // Skip whitespace before low nibble
        while (i < len && is_whitespace(hex_data[i])) {
            i++;
        }
        
        if (i >= len) {
            free(data);
            return -1;
        }
        
        int low = hex_char_to_nibble(hex_data[i]);
        if (low < 0) {
            free(data);
            return -1;
        }
        i++;
        
        data[pos++] = (high << 4) | low;
    }
    
    // Store lift forms
    free(ctx->lift_forms_data);
    ctx->lift_forms_data = data;
    ctx->lift_forms_len = data_len;
    
    return 0;
}

char* atlas_ctx_get_lift_forms_hex(const AtlasBridgeContext* ctx) {
    if (!ctx || !ctx->initialized || !ctx->lift_forms_data) return NULL;
    
    size_t hex_len = ctx->lift_forms_len * 2 + 1;
    char* hex = (char*)malloc(hex_len);
    if (!hex) return NULL;
    
    for (size_t i = 0; i < ctx->lift_forms_len; i++) {
        hex[i * 2] = nibble_to_hex_char(ctx->lift_forms_data[i] >> 4);
        hex[i * 2 + 1] = nibble_to_hex_char(ctx->lift_forms_data[i] & 0x0F);
    }
    hex[hex_len - 1] = '\0';
    
    return hex;
}

// ============================================================================
// Exact Projectors (v0.3)
// ============================================================================

int atlas_ctx_apply_p_class(AtlasBridgeContext* ctx, double* state) {
    if (!ctx || !ctx->initialized || !state) return -1;
    if (!(ctx->config.flags & ATLAS_CTX_ENABLE_P_CLASS)) return -1;
    
    // P_class: exact idempotent projector to class-stable subspace
    // Implementation: projects to constant value per page
    // This ensures P² = P since averaging constant values gives same constants
    
    size_t n_pages = ctx->config.block_size / 256;
    
    // For each page, compute average and replace all bytes with that average
    for (size_t p = 0; p < n_pages; p++) {
        double sum = 0.0;
        
        // Compute sum over all bytes in this page
        for (size_t b = 0; b < 256; b++) {
            sum += state[p * 256 + b];
        }
        
        // Average
        double avg = sum / 256.0;
        
        // Set all bytes to average (making page constant)
        for (size_t b = 0; b < 256; b++) {
            state[p * 256 + b] = avg;
        }
    }
    
    ctx->diag.op_count++;
    return 0;
}

int atlas_ctx_apply_p_299(AtlasBridgeContext* ctx, double* state) {
    if (!ctx || !ctx->initialized || !state) return -1;
    if (!(ctx->config.flags & ATLAS_CTX_ENABLE_P_299)) return -1;
    
    // P_299: reduced-rank projector, trace-zero over page%24 groups
    // Implementation: enforce trace-zero constraint within each group
    // This is idempotent since subtracting the mean twice has same effect as once
    
    size_t n_pages = ctx->config.block_size / 256;
    
    // For each page mod 24 group and each byte position
    for (size_t b = 0; b < 256; b++) {
        for (size_t g = 0; g < 24; g++) {
            // Compute mean over this group at this byte position
            double sum = 0.0;
            size_t count = 0;
            
            for (size_t p = 0; p < n_pages; p++) {
                if (p % 24 == g) {
                    sum += state[p * 256 + b];
                    count++;
                }
            }
            
            if (count == 0) continue;
            
            double mean = sum / count;
            
            // Subtract mean to enforce trace-zero
            for (size_t p = 0; p < n_pages; p++) {
                if (p % 24 == g) {
                    state[p * 256 + b] -= mean;
                }
            }
        }
    }
    
    ctx->diag.op_count++;
    return 0;
}

double atlas_ctx_check_p_class_idempotency(AtlasBridgeContext* ctx, const double* state) {
    if (!ctx || !ctx->initialized || !state) return -1.0;
    
    vec_copy(ctx->temp_buffer, state, ctx->config.block_size);
    vec_copy(ctx->proj_buffer, state, ctx->config.block_size);
    
    // Apply P_class once
    atlas_ctx_apply_p_class(ctx, ctx->temp_buffer);
    
    // Apply P_class twice
    atlas_ctx_apply_p_class(ctx, ctx->proj_buffer);
    atlas_ctx_apply_p_class(ctx, ctx->proj_buffer);
    
    double diff = vec_distance(ctx->temp_buffer, ctx->proj_buffer, ctx->config.block_size);
    ctx->diag.p_class_idempotency = diff;
    return diff;
}

double atlas_ctx_check_p_299_idempotency(AtlasBridgeContext* ctx, const double* state) {
    if (!ctx || !ctx->initialized || !state) return -1.0;
    
    vec_copy(ctx->temp_buffer, state, ctx->config.block_size);
    vec_copy(ctx->proj_buffer, state, ctx->config.block_size);
    
    // Apply P_299 once
    atlas_ctx_apply_p_299(ctx, ctx->temp_buffer);
    
    // Apply P_299 twice
    atlas_ctx_apply_p_299(ctx, ctx->proj_buffer);
    atlas_ctx_apply_p_299(ctx, ctx->proj_buffer);
    
    double diff = vec_distance(ctx->temp_buffer, ctx->proj_buffer, ctx->config.block_size);
    ctx->diag.p_299_idempotency = diff;
    return diff;
}

// ============================================================================
// Co1 Mini-Gates (v0.3)
// ============================================================================

int atlas_ctx_apply_page_rotation(AtlasBridgeContext* ctx, uint32_t rot, double* state) {
    if (!ctx || !ctx->initialized || !state) return -1;
    if (!(ctx->config.flags & ATLAS_CTX_ENABLE_CO1)) return -1;
    
    size_t n_pages = ctx->config.block_size / 256;
    if (rot >= n_pages) rot = rot % n_pages;
    
    if (rot == 0) return 0;  // No-op
    
    // Rotate pages
    vec_copy(ctx->temp_buffer, state, ctx->config.block_size);
    
    for (size_t p = 0; p < n_pages; p++) {
        size_t new_p = (p + rot) % n_pages;
        for (size_t b = 0; b < 256; b++) {
            state[new_p * 256 + b] = ctx->temp_buffer[p * 256 + b];
        }
    }
    
    ctx->diag.op_count++;
    return 0;
}

int atlas_ctx_apply_mix_lifts(AtlasBridgeContext* ctx, double* state) {
    if (!ctx || !ctx->initialized || !state) return -1;
    if (!(ctx->config.flags & ATLAS_CTX_ENABLE_CO1)) return -1;
    
    // Walsh-Hadamard transform on spin-up/spin-down lift components
    // For each (page, byte) pair, apply H = (1/√2) [[1, 1], [1, -1]]
    
    size_t n_pages = ctx->config.block_size / 256;
    
    // Assume first half of pages are spin-up, second half spin-down
    size_t half = n_pages / 2;
    
    for (size_t p = 0; p < half; p++) {
        for (size_t b = 0; b < 256; b++) {
            double up = state[p * 256 + b];
            double down = state[(p + half) * 256 + b];
            
            // Walsh-Hadamard: (|0⟩ + |1⟩)/√2, (|0⟩ - |1⟩)/√2
            double sqrt2_inv = 1.0 / sqrt(2.0);
            state[p * 256 + b] = sqrt2_inv * (up + down);
            state[(p + half) * 256 + b] = sqrt2_inv * (up - down);
        }
    }
    
    ctx->diag.op_count++;
    return 0;
}

int atlas_ctx_apply_page_parity_phase(AtlasBridgeContext* ctx, double* state) {
    if (!ctx || !ctx->initialized || !state) return -1;
    if (!(ctx->config.flags & ATLAS_CTX_ENABLE_CO1)) return -1;
    
    // Apply phase (-1)^parity(page) to each page
    size_t n_pages = ctx->config.block_size / 256;
    
    for (size_t p = 0; p < n_pages; p++) {
        // Count number of 1-bits in page index
        size_t parity = 0;
        size_t pp = p;
        while (pp) {
            parity ^= (pp & 1);
            pp >>= 1;
        }
        
        // Apply phase if parity is 1
        if (parity) {
            for (size_t b = 0; b < 256; b++) {
                state[p * 256 + b] = -state[p * 256 + b];
            }
        }
    }
    
    ctx->diag.op_count++;
    return 0;
}

// ============================================================================
// JSON Certificates and Diagnostics (v0.3)
// ============================================================================

int atlas_ctx_emit_certificate(const AtlasBridgeContext* ctx, const char* filepath, const char* mode) {
    if (!ctx || !ctx->initialized || !filepath || !mode) return -1;
    
    FILE* f = fopen(filepath, "w");
    if (!f) return -1;
    
    fprintf(f, "{\n");
    fprintf(f, "  \"version\": \"%s\",\n", VERSION);
    fprintf(f, "  \"mode\": \"%s\",\n", mode);
    fprintf(f, "  \"timestamp\": %ld,\n", (long)time(NULL));
    fprintf(f, "  \"config\": {\n");
    fprintf(f, "    \"block_size\": %u,\n", ctx->config.block_size);
    fprintf(f, "    \"n_qubits\": %u,\n", ctx->config.n_qubits);
    fprintf(f, "    \"twirl_gens\": %u,\n", ctx->config.twirl_gens);
    fprintf(f, "    \"flags\": %u,\n", ctx->config.flags);
    fprintf(f, "    \"epsilon\": %.12e\n", ctx->config.epsilon);
    fprintf(f, "  },\n");
    fprintf(f, "  \"diagnostics\": {\n");
    fprintf(f, "    \"op_count\": %lu,\n", ctx->diag.op_count);
    fprintf(f, "    \"twirl_idempotency\": %.12e,\n", ctx->diag.twirl_idempotency);
    fprintf(f, "    \"p_class_idempotency\": %.12e,\n", ctx->diag.p_class_idempotency);
    fprintf(f, "    \"p_299_idempotency\": %.12e,\n", ctx->diag.p_299_idempotency);
    fprintf(f, "    \"lift_mass\": %.12e,\n", ctx->diag.lift_mass);
    fprintf(f, "    \"last_residual\": %.12e,\n", ctx->diag.last_residual);
    fprintf(f, "    \"commutant_dim\": %.12e\n", ctx->diag.commutant_dim);
    fprintf(f, "  },\n");
    fprintf(f, "  \"lift_forms\": ");
    
    if (ctx->lift_forms_data && ctx->lift_forms_len > 0) {
        fprintf(f, "\"");
        size_t limit = (ctx->lift_forms_len < CERT_LIFT_FORMS_HEX_LIMIT) 
                       ? ctx->lift_forms_len : CERT_LIFT_FORMS_HEX_LIMIT;
        for (size_t i = 0; i < limit; i++) {
            fprintf(f, "%02x", ctx->lift_forms_data[i]);
        }
        if (ctx->lift_forms_len > CERT_LIFT_FORMS_HEX_LIMIT) {
            fprintf(f, "...");
        }
        fprintf(f, "\"\n");
    } else {
        fprintf(f, "null\n");
    }
    
    fprintf(f, "}\n");
    fclose(f);
    
    return 0;
}

double atlas_ctx_probe_commutant(AtlasBridgeContext* ctx, const double* state, int with_co1) {
    if (!ctx || !ctx->initialized || !state) return -1.0;
    
    // Probe commutant: measure effective dimension of Comm(E, Co1)
    // Simplified: compute variance under random E operations with/without Co1
    
    vec_copy(ctx->temp_buffer, state, ctx->config.block_size);
    vec_zero(ctx->proj_buffer, ctx->config.block_size);
    
    const int n_samples = 10;
    double variance = 0.0;
    
    for (int i = 0; i < n_samples; i++) {
        vec_copy(ctx->twirl_accumulator, ctx->temp_buffer, ctx->config.block_size);
        
        // Apply random E operation
        uint8_t mask = (i * 37) & 0xFF;  // Deterministic "random"
        for (uint8_t q = 0; q < ctx->config.n_qubits; q++) {
            if (mask & (1 << q)) {
                apply_pauli_x_single(ctx->twirl_accumulator, ctx->config.block_size, q);
            }
        }
        
        // Apply Co1 if requested
        if (with_co1) {
            atlas_ctx_apply_page_rotation(ctx, i + 1, ctx->twirl_accumulator);
        }
        
        // Accumulate
        vec_axpy(ctx->proj_buffer, ctx->twirl_accumulator, ctx->config.block_size, 1.0);
    }
    
    // Compute variance (effective dimension)
    vec_scale(ctx->proj_buffer, ctx->config.block_size, 1.0 / n_samples);
    double avg_norm = vec_norm(ctx->proj_buffer, ctx->config.block_size);
    double ref_norm = vec_norm(ctx->temp_buffer, ctx->config.block_size);
    
    // Effective dimension: ratio of norms
    double eff_dim = (ref_norm > 1e-10) ? (avg_norm / ref_norm) : 0.0;
    
    ctx->diag.commutant_dim = eff_dim;
    return eff_dim;
}
