// atlas_core/include/atlas_bridge_ctx.h
// Atlas Bridge Context API v0.3
// Conway–Monster Atlas Upgrade Kit
//
// Provides an opaque context-based API for Atlas bridge operations with:
// - Homomorphic lift permutations via linear forms (Lx, Lz) with runtime swap + hex file loader
// - In-block 8-qubit Pauli/Heisenberg action (block size 12,288, reduced-rank byte axis)
// - E-twirl group action over 16 generators with idempotency (projector stable)
// - Exact idempotent P_class projector and reduced-rank P_299 projector (trace-zero)
// - Co1 mini-gates API: page rotation, Walsh-Hadamard mix, parity phase
// - JSON certificate emission with mode, spinlift, lift forms, projector residuals, commutant probes
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
#define ATLAS_CTX_ENABLE_P_CLASS 0x08
#define ATLAS_CTX_ENABLE_P_299   0x10
#define ATLAS_CTX_ENABLE_CO1     0x20

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
    double p_class_idempotency;  // ||P_class^2 - P_class||_2
    double p_299_idempotency;    // ||P_299^2 - P_299||_2
    double commutant_dim;        // Effective dimension of Comm(E,Co1)
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
// Lift Forms Loader (v0.3)
// ============================================================================

// Load custom lift linear forms from hex file
// filepath: Path to hex file containing 2^{1+24} embedding lift forms
// Returns 0 on success, -1 on error
int atlas_ctx_load_lift_forms(AtlasBridgeContext* ctx, const char* filepath);

// Set lift forms from raw hex data
// hex_data: Hex-encoded string of lift forms
// len: Length of hex string
// Returns 0 on success, -1 on error
int atlas_ctx_set_lift_forms_hex(AtlasBridgeContext* ctx, const char* hex_data, size_t len);

// Get current lift forms as hex string (caller must free)
// Returns NULL on error
char* atlas_ctx_get_lift_forms_hex(const AtlasBridgeContext* ctx);

// ============================================================================
// Exact Projectors (v0.3)
// ============================================================================

// Apply exact idempotent P_class projector
// Projects to class-stable subspace
// state: input/output vector of length block_size
// Returns 0 on success, -1 on error
int atlas_ctx_apply_p_class(AtlasBridgeContext* ctx, double* state);

// Apply reduced-rank P_299 projector (trace-zero over page%24 groups)
// Projects to trace-zero subspace
// state: input/output vector of length block_size
// Returns 0 on success, -1 on error
int atlas_ctx_apply_p_299(AtlasBridgeContext* ctx, double* state);

// Check P_class idempotency: computes ||P(P(v)) - P(v)||_2
// state: test vector of length block_size
// Returns idempotency measure (0.0 = perfect idempotency), -1.0 on error
double atlas_ctx_check_p_class_idempotency(AtlasBridgeContext* ctx, const double* state);

// Check P_299 idempotency: computes ||P(P(v)) - P(v)||_2
// state: test vector of length block_size
// Returns idempotency measure (0.0 = perfect idempotency), -1.0 on error
double atlas_ctx_check_p_299_idempotency(AtlasBridgeContext* ctx, const double* state);

// ============================================================================
// Co1 Mini-Gates (v0.3)
// ============================================================================

// Apply page rotation gate
// rot: Rotation amount (0-47 for 48 pages)
// state: input/output vector of length block_size
// Returns 0 on success, -1 on error
int atlas_ctx_apply_page_rotation(AtlasBridgeContext* ctx, uint32_t rot, double* state);

// Apply Walsh-Hadamard mix on lifts
// Mixes spin-up and spin-down components via Walsh-Hadamard transform
// state: input/output vector of length block_size
// Returns 0 on success, -1 on error
int atlas_ctx_apply_mix_lifts(AtlasBridgeContext* ctx, double* state);

// Apply page parity phase gate
// Applies phase based on parity of page index
// state: input/output vector of length block_size
// Returns 0 on success, -1 on error
int atlas_ctx_apply_page_parity_phase(AtlasBridgeContext* ctx, double* state);

// ============================================================================
// JSON Certificates and Diagnostics (v0.3)
// ============================================================================

// Emit JSON certificate with diagnostics
// filepath: Path to output JSON file
// mode: Mode string (e.g., "spinlift", "commutant")
// Returns 0 on success, -1 on error
int atlas_ctx_emit_certificate(const AtlasBridgeContext* ctx, const char* filepath, const char* mode);

// Compute commutant probe values (with/without Co1 gates)
// Returns effective dimension of Comm(E,Co1), or -1.0 on error
double atlas_ctx_probe_commutant(AtlasBridgeContext* ctx, const double* state, int with_co1);

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
// TODO (v0.4 - 12-qubit extension):
//   - Extend Pauli operators from 8-qubit to full 12-qubit representation
//   - Update block_size calculation for 12-qubit register
//   - Modify twirl generators for expanded Hilbert space
//
// TODO (v0.4 - advanced lift forms):
//   - Implement composite lifts: L_xy = L_x ∘ L_z
//   - Add parameterized lift families with continuous parameters
//   - Support non-homomorphic lift variants for error analysis
//
// TODO (v0.4 - performance optimizations):
//   - SIMD vectorization for Pauli operations and projectors
//   - Sparse matrix representations for large blocks
//   - GPU acceleration hooks for twirl averaging and projector application
//
// TODO (v0.4 - certification enhancements):
//   - Implement formal verification hooks for Lean4 proofs
//   - Export witness data for external validation
//   - Add certificate schema validation
//
// v0.3 CHANGES (current version):
//   ✓ Added lift forms loader with hex file support
//   ✓ Implemented exact P_class and P_299 projectors
//   ✓ Added Co1 mini-gates API (page rotation, mix lifts, parity phase)
//   ✓ Added JSON certificate emission with full diagnostics
//   ✓ Extended unit tests for new features
//   ✓ Maintained full backwards compatibility with v0.2

#ifdef __cplusplus
}
#endif

#endif // ATLAS_BRIDGE_CTX_H
