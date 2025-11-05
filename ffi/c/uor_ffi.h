/*
 * UOR Prime Structure FFI - C API Header
 *
 * This header provides the Foreign Function Interface for the Universal Object
 * Reference (UOR) Prime Structure implementation. The Prime Structure is a
 * 12,288-element mathematical framework (48×256) with resonance compression
 * to 96 classes.
 *
 * Mathematical Foundation:
 * - Unity constraint: α₄α₅ = 1
 * - Resonance compression: 256 → 96 classes (3/8 ratio)
 * - Conservation laws: Triple-cycle invariant (C768)
 * - Holographic principle: Bulk↔boundary correspondence via Φ
 *
 * ABI Stability:
 * The ABI version (UOR_FFI_ABI_VERSION) ensures compatibility. Breaking
 * changes to function signatures or semantics increment this version.
 *
 * Usage:
 * 1. Call lean_initialize_uor() once before using any other functions
 * 2. Use the API functions as needed
 * 3. Call lean_finalize_uor() at process shutdown (optional but recommended)
 *
 * Thread Safety:
 * All functions are thread-safe after initialization is complete.
 */

#ifndef UOR_FFI_H
#define UOR_FFI_H

#include <stdint.h>

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * ABI version for compatibility tracking.
 * Increment on breaking changes to function signatures or semantics.
 */
#define UOR_FFI_ABI_VERSION 1

/*
 * Initialization and Finalization
 *
 * These functions manage the Lean runtime lifecycle.
 */

/**
 * Initialize the UOR library and Lean runtime.
 * Must be called once before using any other functions.
 *
 * @param resv Reserved parameter for future use (pass 0)
 */
void lean_initialize_uor(uintptr_t resv);

/**
 * Finalize the UOR library and clean up Lean runtime.
 * Optional but recommended at process shutdown.
 */
void lean_finalize_uor(void);

/*
 * Prime Structure Constants
 *
 * These functions return the fundamental constants of the Prime Structure.
 */

/**
 * Get the current ABI version.
 * @return ABI version (currently 1)
 */
uint32_t lean_uor_abi_version(void);

/**
 * Get the number of pages in the boundary structure.
 * @return 48 (pages = 3 × 16 = 3 × 2^4)
 */
uint32_t lean_uor_pages(void);

/**
 * Get the number of bytes per page.
 * @return 256 (bytes = 2^8)
 */
uint32_t lean_uor_bytes(void);

/**
 * Get the number of resonance classes after compression.
 * @return 96 (classes = 3 × 32 = 3 × 2^5)
 */
uint32_t lean_uor_rclasses(void);

/*
 * R96 Resonance Classifier
 *
 * Maps byte values to resonance classes, achieving 3/8 compression.
 */

/**
 * Classify a byte into its resonance class.
 *
 * This function implements the resonance classification that compresses
 * 256 byte values into 96 distinct resonance classes, achieving the
 * theoretical 3/8 compression bound.
 *
 * Properties:
 * - Surjective onto [0, 95]
 * - Periodic with period 96
 * - Preserves modular arithmetic structure
 *
 * @param b The byte to classify
 * @return Resonance class in range [0, 95]
 */
uint8_t lean_uor_r96_classify(uint8_t b);

/*
 * Φ Boundary Encoding
 *
 * Functions for packing and unpacking boundary coordinates.
 */

/**
 * Pack (page, byte) coordinates into a 32-bit code.
 *
 * Encoding: (page << 8) | byte
 * This provides efficient coordinate representation for boundary indices.
 *
 * @param page Page coordinate (will be taken modulo 48)
 * @param byte Byte coordinate
 * @return 32-bit packed code
 */
uint32_t lean_uor_phi_encode(uint8_t page, uint8_t byte);

/**
 * Extract page coordinate from encoded value.
 *
 * @param code Encoded boundary code
 * @return Page coordinate (modulo 48)
 */
uint8_t lean_uor_phi_page(uint32_t code);

/**
 * Extract byte coordinate from encoded value.
 *
 * @param code Encoded boundary code
 * @return Byte coordinate (low 8 bits)
 */
uint8_t lean_uor_phi_byte(uint32_t code);

/*
 * Truth ≙ Conservation
 *
 * Budget semantics where truth is defined as zero deficit.
 */

/**
 * Check if a budget represents truth (zero deficit).
 *
 * In the Prime Structure, truth is defined as zero budget (no deficit).
 * This implements the fundamental principle: truth ≙ conservation.
 *
 * @param budget Budget value to check
 * @return 1 if budget is zero (truth), 0 otherwise
 */
uint8_t lean_uor_truth_zero(uint32_t budget);

/**
 * Check truth of budget addition.
 *
 * Truth(a + b) ↔ (Truth a ∧ Truth b)
 * This captures the additive nature of conservation in the budget semantics.
 *
 * @param a First budget value
 * @param b Second budget value
 * @return 1 if a + b equals zero, 0 otherwise
 */
uint8_t lean_uor_truth_add(uint32_t a, uint32_t b);

#ifdef __cplusplus
}
#endif
#endif /* UOR_FFI_H */