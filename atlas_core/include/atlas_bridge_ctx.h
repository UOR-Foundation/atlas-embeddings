// atlas_core/include/atlas_bridge_ctx.h
// Atlas Bridge Context API v0.4
// Conway–Monster Atlas Upgrade Kit
//
// Provides an opaque context-based API for Atlas bridge operations with:
// - Homomorphic lift permutations via linear forms (Lx, Lz) with runtime swap + hex file loader (v0.4: 8-bit mode)
// - In-block 8-qubit Pauli/Heisenberg action (block size 12,288, reduced-rank byte axis) (v0.4: AVX2 acceleration)
// - E-twirl group action over 16 generators with idempotency (projector stable)
// - Exact idempotent P_class projector and reduced-rank P_299 projector (trace-zero) (v0.4: binary matrix loader)
// - Co1 mini-gates API: page rotation, Walsh-Hadamard mix, parity phase (v0.4: real generator loader from co1_gates.txt)
// - JSON certificate emission with mode, spinlift, lift forms, projector residuals, commutant probes
// - Context lifecycle management (new/clone/free)
// - Configuration and diagnostics
// - Block-sparse lift mixing helpers (v0.4: 8x8 double mixing matrix per block)

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
#define ATLAS_CTX_USE_AVX2       0x40  // v0.4: Enable AVX2 SIMD acceleration
#define ATLAS_CTX_LIFT_8BIT      0x80  // v0.4: Use only low 8 bits in lift forms (N_QBITS=8)

// Configuration parameters
typedef struct {
    uint32_t flags;           // Combination of ATLAS_CTX_* flags
    uint32_t block_size;      // Block size (default: 12288 = page*byte)
    uint32_t n_qubits;        // Number of qubits for Pauli ops (default: 8)
    uint32_t twirl_gens;      // Number of E-twirl generators (default: 16)
    double   epsilon;         // Tolerance for idempotency checks (default: 1e-10)
    uint32_t n_qbits;         // v0.4: Number of qubits in lift forms representation (8 or full)
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
    int avx2_available;          // v0.4: 1 if AVX2 acceleration is active, 0 otherwise
    int p_299_exact_loaded;      // v0.4: 1 if exact P_299 matrix loaded from file, 0 for fallback
    int co1_gates_loaded;        // v0.4: 1 if Co1 gates loaded from file, 0 for defaults
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

// Get current lift forms as hex string
// Returns newly allocated string (caller must free with free())
// WARNING: Python/FFI bindings should avoid this function due to memory management complexity
//          Use atlas_ctx_load_lift_forms() or atlas_ctx_set_lift_forms_hex() instead
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
// v0.4 Extensions - Binary Loaders and Advanced Features
// ============================================================================

// Load P_299 matrix from binary file (v0.4)
// filepath: Path to P_299_matrix.bin containing N*N doubles (row-major, symmetric, idempotent)
// If successful, replaces the reduced-rank trace-zero fallback logic with exact matrix
// Returns 0 on success, -1 on error (fallback logic remains active on error)
int atlas_ctx_load_p299_matrix(AtlasBridgeContext* ctx, const char* filepath);

// Load Co1 real generators from text file (v0.4)
// filepath: Path to co1_gates.txt with real-valued generator data
// Works in tandem with binary MAT gates (row-major N*N doubles)
// Returns 0 on success, -1 on error
int atlas_ctx_load_co1_gates(AtlasBridgeContext* ctx, const char* filepath);

// Apply block-sparse lift mixing (v0.4)
// Applies 8x8 double mixing matrix per block for bridge mode lift operations
// block_idx: Index of the block to mix (0 to n_blocks-1)
// mixing_matrix: 8x8 row-major double matrix for mixing
// state: input/output vector of length block_size
// Returns 0 on success, -1 on error
int atlas_ctx_apply_block_mixing(AtlasBridgeContext* ctx, uint32_t block_idx, 
                                   const double* mixing_matrix, double* state);

// Check if AVX2 acceleration is available and active (v0.4)
// Returns 1 if AVX2 is available and flag is set, 0 otherwise
int atlas_ctx_is_avx2_active(const AtlasBridgeContext* ctx);

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
// TODO (v0.5 - 12-qubit extension):
//   - Extend Pauli operators from 8-qubit to full 12-qubit representation
//   - Update block_size calculation for 12-qubit register
//   - Modify twirl generators for expanded Hilbert space
//
// TODO (v0.5 - advanced lift forms):
//   - Implement composite lifts: L_xy = L_x ∘ L_z
//   - Add parameterized lift families with continuous parameters
//   - Support non-homomorphic lift variants for error analysis
//
// TODO (v0.5 - GPU acceleration):
//   - GPU acceleration hooks for twirl averaging and projector application
//   - CUDA/OpenCL backend options
//
// TODO (v0.5 - certification enhancements):
//   - Implement formal verification hooks for Lean4 proofs
//   - Export witness data for external validation
//   - Add certificate schema validation
//
// v0.4 CHANGES (current version):
//   ✓ Added lift forms loader with 8-bit mode support (N_QBITS=8)
//   ✓ Implemented P_299 binary matrix loader (P_299_matrix.bin) with fallback
//   ✓ Added Co1 real generator loader (co1_gates.txt) working with MAT gates
//   ✓ Implemented AVX2 SIMD acceleration for apply_pauli_block hot loops with fallback
//   ✓ Added block-sparse lift mixing helpers (8x8 double matrix per block)
//   ✓ Extended Python bindings for new loaders
//   ✓ Updated CI workflow for AVX2 builds, unit tests, certificate emission
//   ✓ Extended unit tests for P_299 fallback/exact matrix paths
//   ✓ Full backwards compatibility with v0.3
//
// v0.3 CHANGES:
//   ✓ Added lift forms loader with hex file support
//   ✓ Implemented exact P_class and P_299 projectors
//   ✓ Added Co1 mini-gates API (page rotation, mix lifts, parity phase)
//   ✓ Added JSON certificate emission with full diagnostics
//   ✓ Extended unit tests for new features
//   ✓ Maintained full backwards compatibility with v0.2

// ============================================================================
// File Format Specifications (v0.4)
// ============================================================================
//
// lift_forms.hex:
//   - Hex-encoded binary data representing 2^{1+24} embedding lift forms
//   - Each form is a permutation table or linear combination coefficients
//   - When ATLAS_CTX_LIFT_8BIT flag is set, only low 8 bits are used
//   - Format: ASCII hex string, whitespace allowed and ignored
//   - Runtime swappable via atlas_ctx_load_lift_forms() or atlas_ctx_set_lift_forms_hex()
//
// P_299_matrix.bin:
//   - Binary file containing N*N doubles in row-major order (N = block_size)
//   - Matrix must be symmetric and idempotent (P² = P) to within numerical tolerance
//   - Used for exact dense P_299 projector when available
//   - If absent or load fails, falls back to reduced-rank trace-zero logic
//   - File size: N*N*sizeof(double) bytes
//   - Endianness: native (same as compile platform)
//
// co1_gates.txt:
//   - Text file with real-valued Co1 generator data
//   - One generator per line or section
//   - Works in tandem with binary MAT gates (row-major N*N doubles)
//   - Format details: Each line may specify generator index, real coefficients
//   - Comments start with # and are ignored
//   - Blank lines ignored
//
// Block-sparse mixing matrices:
//   - Each block has an 8x8 double precision mixing matrix
//   - Applied via atlas_ctx_apply_block_mixing()
//   - Matrix is row-major, applied as: out = M * in for each 8-element sub-block
//   - Useful for bridge mode lift operations with structured sparsity

// ============================================================================
// Performance and Implementation Notes (v0.4)
// ============================================================================
//
// AVX2 Acceleration:
//   - When ATLAS_CTX_USE_AVX2 flag is set and AVX2 is available at runtime,
//     hot loops in apply_pauli_block use 256-bit SIMD intrinsics
//   - Fallback to scalar code if AVX2 unavailable or flag not set
//   - Detection at context creation time via CPUID (x86/x64) or compile-time flags
//   - Speedup: typically 2-4x for Pauli X/Z operations on large blocks
//
// P_299 Matrix Loading:
//   - Exact matrix is preferred when available (better numerical accuracy)
//   - Fallback reduced-rank logic is trace-zero projector (faster, approximate)
//   - Idempotency check performed on loaded matrix: ||P²-P||_F < epsilon
//   - Memory: O(N²) for exact matrix, O(N) for fallback
//
// Co1 Gate Loading:
//   - Real generators complement binary MAT gate representation
//   - Allows hybrid classical/quantum gate synthesis
//   - Compatible with existing Co1 mini-gates API (page rotation, etc.)
//
// Wiring Summary:
//   - Lift forms: hex loader → internal byte buffer → runtime swap via Lx/Lz
//   - P_299: binary loader → dense matrix buffer OR fallback trace-zero logic
//   - Co1 gates: text loader → real coefficient array → tandem with MAT gates
//   - Block mixing: 8x8 matrix per block → applied in lift bridge mode
//   - AVX2: compile-time + runtime detection → hot loop dispatch → fallback scalar

#ifdef __cplusplus
}
#endif

#endif // ATLAS_BRIDGE_CTX_H
