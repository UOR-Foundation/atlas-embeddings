/**
 * Lift: Class Index → SGA Element
 *
 * This module implements the lift function that converts class indices
 * to SGA rank-1 basis elements.
 *
 * For a class with coordinates (h, d, ℓ):
 *   E_{h,d,ℓ} = r^h ⊗ e_ℓ ⊗ τ^d
 *
 * where:
 *   - h ∈ ℤ₄ (quadrant/scope)
 *   - d ∈ ℤ₃ (modality/triality)
 *   - ℓ ∈ ℤ₈ (context slot, where ℓ=0 represents the scalar)
 */

import type { SgaElement } from '../sga/types';
import { createRank1Basis } from '../sga/sga-element';
import { decodeClassIndex } from '../class-system/class';

/**
 * Lift a class index to an SGA rank-1 basis element
 *
 * @param classIndex - Class index (0..95)
 * @returns SGA element E_{h,d,ℓ} = r^h ⊗ e_ℓ ⊗ τ^d
 */
export function lift(classIndex: number): SgaElement {
  if (classIndex < 0 || classIndex >= 96) {
    throw new Error(`Invalid class index: ${classIndex}. Must be 0..95.`);
  }

  // Decode class index to components (h₂, d, ℓ)
  const { h2, d, l } = decodeClassIndex(classIndex);

  // Create rank-1 basis element
  // Note: h2 in class system = h in SGA (both are ℤ₄)
  return createRank1Basis(h2, d, l);
}

/**
 * Lift all 96 classes to SGA elements
 *
 * @returns Array of 96 SGA elements, indexed by class index
 */
export function liftAll(): SgaElement[] {
  return Array.from({ length: 96 }, (_, i) => lift(i));
}

/**
 * Lift multiple class indices
 *
 * @param indices - Array of class indices
 * @returns Array of corresponding SGA elements
 */
export function liftMultiple(indices: number[]): SgaElement[] {
  return indices.map((i) => lift(i));
}
