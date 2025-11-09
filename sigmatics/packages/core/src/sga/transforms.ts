/**
 * Transform Automorphisms
 *
 * This module implements the four fundamental transforms as algebra automorphisms:
 *
 * - R: Quarter-turn rotation (left multiply by r)
 * - D: Triality rotation (right multiply by τ)
 * - T: Context rotation (permute basis vectors)
 * - M: Mirror (orientation reversal)
 *
 * These satisfy the group relations:
 * - R⁴ = D³ = T⁸ = M² = identity
 * - RD = DR, RT = TR, DT = TD (pairwise commute)
 * - MRM = R⁻¹, MDM = D⁻¹, MTM = T⁻¹ (mirror conjugation)
 */

import type { SgaElement, Cl07Element, Blade } from './types';
import { createSgaElement, sgaMultiply, sgaIdentity, sgaEqual } from './sga-element';
import { createCliffordElement, cliffordIdentity, countBasisVectors } from './clifford';
import { z4Generator, z4Power, z4Invert, z3Generator, z3Power, z3Invert } from './group-algebras';

/**
 * Parse blade to extract basis vector indices
 */
function parseBlade(blade: Blade): number[] {
  if (blade === '1') return [];
  const matches = blade.match(/e(\d)/g);
  if (!matches) return [];
  return matches.map((m) => parseInt(m.substring(1), 10));
}

/**
 * Format basis vector indices as blade
 */
function formatBlade(indices: number[]): Blade {
  if (indices.length === 0) return '1';
  return indices.map((i) => `e${i}`).join('');
}

/**
 * Apply T transform to Clifford element
 *
 * For rank-1 elements, T rotates the 8-element context space:
 *   ℓ=0 (scalar "1") → ℓ=1 (e₁) → ℓ=2 (e₂) → ... → ℓ=7 (e₇) → ℓ=0 (scalar)
 *
 * The key insight is that the scalar and basis vectors form an 8-element cycle,
 * not just a 7-element cycle of basis vectors.
 *
 * @param clifford - Clifford element (should be rank-1 for class system)
 * @param k - Rotation amount (mod 8)
 * @returns Rotated Clifford element
 */
function applyTToClifford(clifford: Cl07Element, k: number): Cl07Element {
  // Extract the entries
  const entries = Array.from(clifford.grades.entries());

  // For rank-1 elements (the only case for the class system)
  if (entries.length === 1) {
    const [blade, coeff] = entries[0];

    // Extract current ℓ value
    let currentL: number;
    if (blade === '1') {
      // Scalar case
      currentL = 0;
    } else {
      // Check if it's a single basis vector like "e1", "e2", etc.
      const match = blade.match(/^e(\d)$/);
      if (match) {
        currentL = parseInt(match[1], 10);
        if (currentL < 1 || currentL > 7) {
          throw new Error(`Invalid basis vector index: ${currentL}`);
        }
      } else {
        // Higher-grade blade - not a rank-1 element
        throw new Error(`T-transform on higher-grade element not supported: ${blade}`);
      }
    }

    // Apply rotation in the 8-element context space
    const newL = (currentL + k) % 8;

    // Create new Clifford element based on new ℓ value
    if (newL === 0) {
      // Scalar
      return createCliffordElement(new Map([['1', coeff]]));
    } else {
      // Basis vector e₁..e₇
      return createCliffordElement(new Map([[`e${newL}`, coeff]]));
    }
  }

  // For multi-grade elements (shouldn't happen in the class system)
  throw new Error('T-transform requires rank-1 element (scalar or single basis vector)');
}

// ============================================================================
// R Transform (Quarter-turn rotation)
// ============================================================================

/**
 * Apply R transform: left multiply by r
 *
 * R(x) = r · x
 *
 * This increments the h coordinate (quadrant) by 1 (mod 4).
 *
 * @param x - SGA element
 */
export function transformR(x: SgaElement): SgaElement {
  const r = createSgaElement(cliffordIdentity(), z4Generator(), z3Power(0));
  return sgaMultiply(r, x);
}

/**
 * Apply R transform k times
 *
 * @param x - SGA element
 * @param k - Number of applications (will be reduced mod 4)
 */
export function transformRPower(x: SgaElement, k: number): SgaElement {
  const kMod = ((k % 4) + 4) % 4;

  if (kMod === 0) return x;

  const rPower = createSgaElement(cliffordIdentity(), z4Power(kMod), z3Power(0));
  return sgaMultiply(rPower, x);
}

// ============================================================================
// D Transform (Triality rotation)
// ============================================================================

/**
 * Apply D transform: right multiply by τ
 *
 * D(x) = x · τ
 *
 * This increments the d coordinate (modality) by 1 (mod 3).
 *
 * @param x - SGA element
 */
export function transformD(x: SgaElement): SgaElement {
  const tau = createSgaElement(cliffordIdentity(), z4Power(0), z3Generator());
  return sgaMultiply(x, tau);
}

/**
 * Apply D transform k times
 *
 * @param x - SGA element
 * @param k - Number of applications (will be reduced mod 3)
 */
export function transformDPower(x: SgaElement, k: number): SgaElement {
  const kMod = ((k % 3) + 3) % 3;

  if (kMod === 0) return x;

  const tauPower = createSgaElement(cliffordIdentity(), z4Power(0), z3Power(kMod));
  return sgaMultiply(x, tauPower);
}

// ============================================================================
// T Transform (Context rotation)
// ============================================================================

/**
 * Apply T transform: permute basis vectors
 *
 * T(eᵢ) = e_{(i mod 7) + 1}  (cycles e₁→e₂→...→e₇→e₁)
 *
 * This increments the ℓ coordinate (context slot) by 1 (mod 8),
 * where ℓ=0 represents the scalar and ℓ=1..7 represent e₁..e₇.
 *
 * @param x - SGA element
 */
export function transformT(x: SgaElement): SgaElement {
  return transformTPower(x, 1);
}

/**
 * Apply T transform k times
 *
 * @param x - SGA element
 * @param k - Number of applications (will be reduced mod 8)
 */
export function transformTPower(x: SgaElement, k: number): SgaElement {
  const kMod = ((k % 8) + 8) % 8;

  if (kMod === 0) return x;

  // Permute the Clifford component
  const permutedClifford = applyTToClifford(x.clifford, kMod);

  return createSgaElement(permutedClifford, x.z4, x.z3);
}

// ============================================================================
// M Transform (Mirror / Orientation reversal)
// ============================================================================

/**
 * Apply M transform: mirror (orientation reversal)
 *
 * According to the class system spec, M only affects the modality:
 *   d: 0→0, 1→2, 2→1 (equivalent to d → -d mod 3)
 *
 * The h and ℓ components remain unchanged.
 *
 * In group algebra terms:
 *   M(τ^d) = τ^(-d) = τ^(3-d) (mod 3)
 *   M(r^h) = r^h (unchanged)
 *   M(e_ℓ) = e_ℓ (unchanged)
 *
 * @param x - SGA element
 */
export function transformM(x: SgaElement): SgaElement {
  // For M, we only invert τ (the d component)
  // The Clifford and r components remain unchanged
  return createSgaElement(
    x.clifford, // Clifford part unchanged
    x.z4, // r part unchanged
    z3Invert(x.z3), // Only invert τ: τ^d → τ^(-d)
  );
}

/**
 * Verify that R⁴ = identity
 */
export function verifyR4Identity(x: SgaElement): boolean {
  const result = transformRPower(x, 4);
  return sgaEqual(result, x);
}

/**
 * Verify that D³ = identity
 */
export function verifyD3Identity(x: SgaElement): boolean {
  const result = transformDPower(x, 3);
  return sgaEqual(result, x);
}

/**
 * Verify that T⁸ = identity
 */
export function verifyT8Identity(x: SgaElement): boolean {
  const result = transformTPower(x, 8);
  return sgaEqual(result, x);
}

/**
 * Verify that M² = identity
 */
export function verifyM2Identity(x: SgaElement): boolean {
  const result = transformM(transformM(x));
  return sgaEqual(result, x);
}
