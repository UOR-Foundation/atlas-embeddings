// atlas_core/include/atlas_bridge_ctx.h
// Atlas Bridge Context API v0.2
// Conway–Monster Atlas Upgrade Kit
//
// Provides an opaque context-based API for Atlas bridge operations with:
// - Homomorphic lift permutations via linear forms (Lx, Lz)
// - In-block 8-qubit Pauli/Heisenberg action (block size 12,288, reduced-rank byte axis)
// - E-twirl group action over 16 generators with idempotency (projector stable)
// - Context lifecycle management (new/clone/free)
// - Configuration and diagnostics

#ifndef ATLAS_BRIDGE_CTX_H
#define ATLAS_BRIDGE_CTX_H

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

// Opaque context handle
typedef struct AtlasBridgeContext AtlasBridgeContext;

// Context creation flags
#define ATLAS_CTX_DEFAULT       0x00
#define ATLAS_CTX_ENABLE_TWIRL  0x01
#define ATLAS_CTX_ENABLE_LIFT   0x02
#define ATLAS_CTX_VERBOSE       0x04

// Configuration parameters
typedef struct {
    uint32_t flags;           // Combination of ATLAS_CTX_* flags
    uint32_t block_size;      // Block size (default: 12288 = page*byte)
    uint32_t n_qubits;        // Number of qubits for Pauli ops (default: 8)
    uint32_t twirl_gens;      // Number of E-twirl generators (default: 16)
    double   epsilon;         // Tolerance for idempotency checks (default: 1e-10)
} AtlasContextConfig;

// Diagnostics structure
typedef struct {
    double twirl_idempotency; // ||T^2 - T||_2 where T is twirl projector
    double lift_mass;         // Accumulated mass after lift permutation
    uint64_t op_count;        // Number of operations performed
    double last_residual;     // Last computed residual
} AtlasContextDiagnostics;

// ============================================================================
// Context Lifecycle
// ============================================================================

// Create new context with given configuration
// Returns NULL on failure
AtlasBridgeContext* atlas_ctx_new(const AtlasContextConfig* config);

// Create new context with default configuration
// Equivalent to atlas_ctx_new(NULL)
AtlasBridgeContext* atlas_ctx_new_default(void);

// Clone an existing context (deep copy)
// Returns NULL on failure
AtlasBridgeContext* atlas_ctx_clone(const AtlasBridgeContext* ctx);

// Free context and release resources
void atlas_ctx_free(AtlasBridgeContext* ctx);

// ============================================================================
// Configuration
// ============================================================================

// Get current configuration (returns 0 on success, -1 on error)
int atlas_ctx_get_config(const AtlasBridgeContext* ctx, AtlasContextConfig* config);

// Update configuration (returns 0 on success, -1 on error)
// Note: Some parameters may not be updatable after creation
int atlas_ctx_set_config(AtlasBridgeContext* ctx, const AtlasContextConfig* config);

// Get default configuration
void atlas_ctx_config_default(AtlasContextConfig* config);

// ============================================================================
// Homomorphic Lift Permutations
// ============================================================================

// Apply homomorphic lift permutation via linear form Lx
// Operates on in-block structure with reduced-rank (byte axis)
// state: input/output vector of length block_size
// Returns 0 on success, -1 on error
int atlas_ctx_apply_lift_x(AtlasBridgeContext* ctx, double* state);

// Apply homomorphic lift permutation via linear form Lz
// Operates on in-block structure with reduced-rank (byte axis)
// state: input/output vector of length block_size
// Returns 0 on success, -1 on error
int atlas_ctx_apply_lift_z(AtlasBridgeContext* ctx, double* state);

// ============================================================================
// In-Block Pauli/Heisenberg Action
// ============================================================================

// Apply 8-qubit Pauli X operator on specified qubit subset
// qubit_mask: bitmask specifying which qubits to apply X (up to 8 bits)
// state: input/output vector of length block_size
// Returns 0 on success, -1 on error
int atlas_ctx_apply_pauli_x(AtlasBridgeContext* ctx, uint8_t qubit_mask, double* state);

// Apply 8-qubit Pauli Z operator on specified qubit subset
// qubit_mask: bitmask specifying which qubits to apply Z (up to 8 bits)
// state: input/output vector of length block_size
// Returns 0 on success, -1 on error
int atlas_ctx_apply_pauli_z(AtlasBridgeContext* ctx, uint8_t qubit_mask, double* state);

// Apply Heisenberg exchange operator on specified qubit pair
// Implements sigma_i · sigma_j on qubits i and j
// q1, q2: qubit indices (0-7)
// state: input/output vector of length block_size
// Returns 0 on success, -1 on error
int atlas_ctx_apply_heisenberg(AtlasBridgeContext* ctx, uint8_t q1, uint8_t q2, double* state);

// ============================================================================
// E-Twirl Group Action
// ============================================================================

// Apply E-twirl projector (averaging over group generators)
// Uses pre-computed generator set (default: 16 generators)
// Idempotent: T^2 = T (up to numerical tolerance)
// state: input/output vector of length block_size
// Returns 0 on success, -1 on error
int atlas_ctx_apply_twirl(AtlasBridgeContext* ctx, double* state);

// Check E-twirl idempotency: computes ||T(T(v)) - T(v)||_2
// state: test vector of length block_size
// Returns idempotency measure (0.0 = perfect idempotency)
// Returns -1.0 on error
double atlas_ctx_check_twirl_idempotency(AtlasBridgeContext* ctx, const double* state);

// Get E-twirl generator at specified index
// gen_idx: generator index (0 to twirl_gens-1)
// x_mask, z_mask: output 8-bit Pauli masks (can be NULL)
// Returns 0 on success, -1 on error
int atlas_ctx_get_twirl_generator(const AtlasBridgeContext* ctx, uint32_t gen_idx,
                                   uint8_t* x_mask, uint8_t* z_mask);

// ============================================================================
// Diagnostics
// ============================================================================

// Get current diagnostics (returns 0 on success, -1 on error)
int atlas_ctx_get_diagnostics(const AtlasBridgeContext* ctx, AtlasContextDiagnostics* diag);

// Reset diagnostics counters
void atlas_ctx_reset_diagnostics(AtlasBridgeContext* ctx);

// Validate internal consistency
// Returns 0 if consistent, -1 if errors detected
int atlas_ctx_validate(const AtlasBridgeContext* ctx);

// Print diagnostics to stdout (for debugging)
void atlas_ctx_print_diagnostics(const AtlasBridgeContext* ctx);

// ============================================================================
// Utility Functions
// ============================================================================

// Get library version string
const char* atlas_ctx_version(void);

// Get block size for current context
uint32_t atlas_ctx_get_block_size(const AtlasBridgeContext* ctx);

// Get number of qubits for current context
uint32_t atlas_ctx_get_n_qubits(const AtlasBridgeContext* ctx);

// ============================================================================
// Future Upgrade Notes (for maintainers)
// ============================================================================
//
// TODO (12-qubit extension):
//   - Extend Pauli operators from 8-qubit to full 12-qubit representation
//   - Update block_size calculation for 12-qubit register
//   - Modify twirl generators for expanded Hilbert space
//
// TODO (advanced lift forms):
//   - Implement composite lifts: L_xy = L_x ∘ L_z
//   - Add parameterized lift families with continuous parameters
//   - Support non-homomorphic lift variants for error analysis
//
// TODO (wiring Co1 gates):
//   - Integrate Co1 gate family from atlas_bridge.h
//   - Add context-aware Co1 application with twirl compatibility
//   - Implement Co1-invariant projector subspaces
//   - Cross-reference: see atlas_core/src/co1_gates.c for gate implementations
//
// TODO (performance optimizations):
//   - SIMD vectorization for Pauli operations
//   - Sparse matrix representations for large blocks
//   - GPU acceleration hooks for twirl averaging
//
// TODO (certification):
//   - Add certificate generation for twirl idempotency
//   - Implement formal verification hooks for Lean4 proofs
//   - Export witness data for external validation

#ifdef __cplusplus
}
#endif

#endif // ATLAS_BRIDGE_CTX_H
