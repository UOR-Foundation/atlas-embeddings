// atlas/include/e_layer.h
// E-Layer: Extraspecial 2-group formalization
// Conway–Monster Atlas Upgrade Kit v1.1
//
// Mathematical foundation documented in:
// - lean4/Math/Heisenberg/Core.lean
// - lean4/Math/Pauli/Commutator.lean
// - docs/heisenberg_clifford.md

#ifndef E_LAYER_H
#define E_LAYER_H

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

// ============================================================================
// E-Layer Group Structure
// ============================================================================

/**
 * E group element: extraspecial 2-group extension
 * 
 * Mathematical structure: 1 → Z/2 → E → (Z/2)^12 → 1
 * Representation: (phase, x, z) where x, z ∈ F_2^12
 * 
 * Group operation: (s₁, x₁, z₁) * (s₂, x₂, z₂) = 
 *                  (s₁ + s₂ + ω((x₁,z₁), (x₂,z₂)), x₁ + x₂, z₁ + z₂)
 * 
 * where ω is the symplectic form: ω((x₁,z₁), (x₂,z₂)) = x₁·z₂ + z₁·x₂ (mod 2)
 */
typedef struct {
    uint64_t x_bits;  // X-type support (12 qubits, bits 0-11)
    uint64_t z_bits;  // Z-type support (12 qubits, bits 0-11)
    uint8_t phase;    // Phase factor (0, 1, 2, 3 for i^phase)
} EGroupElement;

// ============================================================================
// Basic E-Group Operations
// ============================================================================

/**
 * Initialize E group element to identity
 */
void e_group_init(EGroupElement* elem);

/**
 * Multiply two E group elements using cocycle formula
 * result = a * b
 * 
 * Implements: (s₁, v₁) * (s₂, v₂) = (s₁ + s₂ + ω(v₁, v₂), v₁ + v₂)
 * 
 * References: Math.Heisenberg.Core.mul
 */
void e_group_multiply(EGroupElement* result, const EGroupElement* a, const EGroupElement* b);

/**
 * Compute inverse of E group element
 * result = a^{-1}
 * 
 * In characteristic 2: (s, v)^{-1} = (s, v) since v^{-1} = v and ω(v,v) = 0
 * 
 * References: Math.Heisenberg.Core.inv
 */
void e_group_inverse(EGroupElement* result, const EGroupElement* a);

/**
 * Check if two elements are equal
 */
int e_group_equal(const EGroupElement* a, const EGroupElement* b);

// ============================================================================
// Symplectic Form
// ============================================================================

/**
 * Compute symplectic form ω((x₁,z₁), (x₂,z₂)) = x₁·z₂ + z₁·x₂ (mod 2)
 * 
 * This determines commutation relations:
 * [a, b] commutes iff ω(a.v, b.v) = 0
 * 
 * Returns: 0 or 1
 * 
 * References: Math.Heisenberg.Core.symplecticForm
 */
uint8_t e_symplectic_form(const EGroupElement* a, const EGroupElement* b);

/**
 * Verify symplectic form is alternating: ω(v, v) = 0
 * Returns: 1 if satisfied, 0 otherwise
 * 
 * References: Math.Heisenberg.Core.symplectic_alternating
 */
int e_verify_alternating(void);

/**
 * Verify symplectic form is antisymmetric: ω(v₁, v₂) = ω(v₂, v₁) in char 2
 * Returns: 1 if satisfied, 0 otherwise
 * 
 * References: Math.Heisenberg.Core.symplectic_antisym
 */
int e_verify_antisymmetric(void);

// ============================================================================
// Center Operations
// ============================================================================

/**
 * Create center element: (phase, 0, 0)
 * The center consists of {I, -I} where -I has phase=2
 * 
 * References: Math.Heisenberg.Core.center
 */
void e_center_element(EGroupElement* elem, uint8_t phase);

/**
 * Check if element is in center (x_bits = 0, z_bits = 0)
 * 
 * References: Math.Heisenberg.Core.mem_center_iff
 */
int e_group_is_central(const EGroupElement* elem);

// ============================================================================
// Commutator Operations
// ============================================================================

/**
 * Compute commutator [a, b] = a * b * a^{-1} * b^{-1}
 * 
 * For Heisenberg group: [a, b] = center(ω(a.v, b.v))
 * 
 * References: Math.Heisenberg.Core.commutator_eq_center
 */
void e_group_commutator(EGroupElement* result, const EGroupElement* a, const EGroupElement* b);

// ============================================================================
// Pauli Basis Elements
// ============================================================================

/**
 * Create X-type Pauli element: X_i
 * X_i has x_bits with bit i set, z_bits = 0, phase = 0
 * 
 * References: Math.Pauli.Commutator.X_basis
 */
void e_pauli_X(EGroupElement* elem, int i);

/**
 * Create Z-type Pauli element: Z_i
 * Z_i has z_bits with bit i set, x_bits = 0, phase = 0
 * 
 * References: Math.Pauli.Commutator.Z_basis
 */
void e_pauli_Z(EGroupElement* elem, int i);

/**
 * Create Y-type Pauli element: Y_i = X_i * Z_i
 * Y_i has both x_bits and z_bits with bit i set
 * 
 * References: Math.Pauli.Commutator.Y_basis
 */
void e_pauli_Y(EGroupElement* elem, int i);

// ============================================================================
// State Vector Application
// ============================================================================

/**
 * Apply E group element to state vector
 * 
 * Action: (s, x, z)|b⟩ = (-1)^{s + z·b} |b ⊕ x⟩
 * 
 * Parameters:
 * - elem: E group element to apply
 * - state: State vector (length dim)
 * - dim: Dimension of state space (should be 2^12 = 4096 for n=12)
 * 
 * References: Math.Heisenberg.StoneVonNeumannProof.π_std
 */
void e_group_apply_to_state(const EGroupElement* elem, double* state, size_t dim);

// ============================================================================
// Quotient Operations
// ============================================================================

/**
 * Project to quotient H/{±I} → (F₂)^24
 * Extracts the vector part (x_bits, z_bits), discarding phase
 * 
 * References: AtlasEmbeddings.ELayer.quotient_map
 */
void e_quotient_project(const EGroupElement* elem, uint64_t* x_out, uint64_t* z_out);

/**
 * Create element from quotient representative
 * Creates element (0, x, z) with trivial phase
 */
void e_from_quotient(EGroupElement* elem, uint64_t x, uint64_t z);

// ============================================================================
// Testing and Verification
// ============================================================================

/**
 * Verify group axioms on sample elements
 * Returns: 1 if all axioms pass, 0 otherwise
 */
int e_verify_group_axioms(void);

/**
 * Verify commutation relations: [X_i, Z_j] = δ_ij * center(1)
 * Returns: 1 if all relations hold, 0 otherwise
 * 
 * References: Math.Pauli.Commutator.canonical_commutation_relation
 */
int e_verify_commutation_relations(void);

/**
 * Verify connection to 12,288-cell boundary
 * Returns: 1 if structure is consistent, 0 otherwise
 * 
 * References: AtlasEmbeddings.ELayer.base_space_dim
 */
int e_verify_atlas_connection(void);

// ============================================================================
// Clifford Normalizer Helpers
// ============================================================================

/**
 * Check if a transformation preserves the symplectic form
 * Used for verifying Clifford group elements
 * 
 * References: Math.Clifford.Normalizer.PreservesSymplectic
 */
int e_preserves_symplectic(
    const EGroupElement* input1, const EGroupElement* input2,
    const EGroupElement* output1, const EGroupElement* output2);

// ============================================================================
// Utility Functions
// ============================================================================

/**
 * Print E group element in human-readable format
 */
void e_group_print(const EGroupElement* elem);

/**
 * Convert masks to E group element
 */
void e_masks_to_element(EGroupElement* elem, const uint64_t* x_mask, const uint64_t* z_mask);

#ifdef __cplusplus
}
#endif

#endif // E_LAYER_H
