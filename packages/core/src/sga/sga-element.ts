/**
 * SGA Element Implementation
 *
 * This module implements the main SgaElement class representing elements
 * of the Sigmatics Geometric Algebra:
 *
 *   SGA = Cl₀,₇ ⊗ ℝ[ℤ₄] ⊗ ℝ[ℤ₃]
 *
 * The product is the tensor product of the three algebra products.
 */

import type { SgaElement, Cl07Element, Z4Element, Z3Element, Rank1Basis } from './types';
import { EPSILON } from './types';
import {
  cliffordIdentity,
  cliffordZero,
  cliffordEqual,
  cliffordAdd,
  cliffordScale,
  geometricProduct,
  gradeInvolution,
  reversion,
  cliffordConjugation,
  basisVector,
} from './clifford';
import {
  z4Identity,
  z4Zero,
  z4Equal,
  z4Add,
  z4Scale,
  z4Multiply,
  z4Power,
  z3Identity,
  z3Zero,
  z3Equal,
  z3Add,
  z3Scale,
  z3Multiply,
  z3Power,
} from './group-algebras';

/**
 * Create an SGA element from its components
 *
 * @param clifford - Clifford algebra component
 * @param z4 - ℝ[ℤ₄] component
 * @param z3 - ℝ[ℤ₃] component
 */
export function createSgaElement(clifford: Cl07Element, z4: Z4Element, z3: Z3Element): SgaElement {
  return { clifford, z4, z3 };
}

/**
 * Create the identity element of SGA
 *
 * 1 ⊗ r⁰ ⊗ τ⁰
 */
export function sgaIdentity(): SgaElement {
  return createSgaElement(cliffordIdentity(), z4Identity(), z3Identity());
}

/**
 * Create the zero element of SGA
 */
export function sgaZero(): SgaElement {
  return createSgaElement(cliffordZero(), z4Zero(), z3Zero());
}

/**
 * Create a rank-1 basis element E_{h,d,ℓ} = r^h ⊗ e_ℓ ⊗ τ^d
 *
 * @param h - Quadrant index (0..3)
 * @param d - Triality index (0..2)
 * @param l - Context index (0..7, where 0 represents scalar)
 */
export function createRank1Basis(h: number, d: number, l: number): SgaElement {
  // For l=0, use scalar (identity in Clifford algebra)
  // For l=1..7, use basis vector e_l
  const clifford = l === 0 ? cliffordIdentity() : basisVector(l);

  return createSgaElement(clifford, z4Power(h), z3Power(d));
}

/**
 * Create a rank-1 basis element from Rank1Basis coordinates
 */
export function createRank1BasisFromCoords(coords: Rank1Basis): SgaElement {
  return createRank1Basis(coords.h, coords.d, coords.l);
}

/**
 * Multiply two SGA elements
 *
 * The product is the tensor product:
 * (a ⊗ r^h ⊗ τ^d) · (b ⊗ r^h' ⊗ τ^d') = (a·b) ⊗ r^(h+h') ⊗ τ^(d+d')
 *
 * @param x - First element
 * @param y - Second element
 */
export function sgaMultiply(x: SgaElement, y: SgaElement): SgaElement {
  return createSgaElement(
    geometricProduct(x.clifford, y.clifford),
    z4Multiply(x.z4, y.z4),
    z3Multiply(x.z3, y.z3),
  );
}

/**
 * Add two SGA elements
 */
export function sgaAdd(x: SgaElement, y: SgaElement): SgaElement {
  return createSgaElement(
    cliffordAdd(x.clifford, y.clifford),
    z4Add(x.z4, y.z4),
    z3Add(x.z3, y.z3),
  );
}

/**
 * Scale an SGA element by a real scalar
 */
export function sgaScale(x: SgaElement, scalar: number): SgaElement {
  return createSgaElement(
    cliffordScale(x.clifford, scalar),
    z4Scale(x.z4, scalar),
    z3Scale(x.z3, scalar),
  );
}

/**
 * Test equality of two SGA elements
 *
 * @param x - First element
 * @param y - Second element
 * @param epsilon - Tolerance for floating-point comparison
 */
export function sgaEqual(x: SgaElement, y: SgaElement, epsilon = EPSILON): boolean {
  return (
    cliffordEqual(x.clifford, y.clifford, epsilon) &&
    z4Equal(x.z4, y.z4, epsilon) &&
    z3Equal(x.z3, y.z3, epsilon)
  );
}

/**
 * Grade involution extended to SGA
 *
 * Applies grade involution to Clifford component, leaves z4 and z3 unchanged
 */
export function sgaGradeInvolution(x: SgaElement): SgaElement {
  return createSgaElement(gradeInvolution(x.clifford), x.z4, x.z3);
}

/**
 * Reversion extended to SGA
 *
 * Applies reversion to Clifford component, leaves z4 and z3 unchanged
 */
export function sgaReversion(x: SgaElement): SgaElement {
  return createSgaElement(reversion(x.clifford), x.z4, x.z3);
}

/**
 * Clifford conjugation extended to SGA
 *
 * Applies Clifford conjugation to Clifford component, leaves z4 and z3 unchanged
 */
export function sgaCliffordConjugation(x: SgaElement): SgaElement {
  return createSgaElement(cliffordConjugation(x.clifford), x.z4, x.z3);
}

/**
 * Compute powers of an SGA element
 *
 * @param x - Base element
 * @param n - Exponent (non-negative integer)
 */
export function sgaPower(x: SgaElement, n: number): SgaElement {
  if (n < 0) {
    throw new Error('Negative powers not supported');
  }

  if (n === 0) {
    return sgaIdentity();
  }

  let result = x;
  for (let i = 1; i < n; i++) {
    result = sgaMultiply(result, x);
  }

  return result;
}

/**
 * Check if an SGA element is the zero element
 */
export function sgaIsZero(x: SgaElement, epsilon = EPSILON): boolean {
  return sgaEqual(x, sgaZero(), epsilon);
}

/**
 * Check if an SGA element is the identity element
 */
export function sgaIsIdentity(x: SgaElement, epsilon = EPSILON): boolean {
  return sgaEqual(x, sgaIdentity(), epsilon);
}

/**
 * Format an SGA element as a string (for debugging)
 */
export function sgaToString(x: SgaElement): string {
  const cliffordStr = Array.from(x.clifford.grades.entries())
    .map(([blade, coeff]) => `${coeff.toFixed(3)}·${blade}`)
    .join(' + ');

  const z4Str = x.z4.coefficients
    .map((c, i) => (Math.abs(c) >= EPSILON ? `${c.toFixed(3)}·r^${i}` : ''))
    .filter((s) => s)
    .join(' + ');

  const z3Str = x.z3.coefficients
    .map((c, i) => (Math.abs(c) >= EPSILON ? `${c.toFixed(3)}·τ^${i}` : ''))
    .filter((s) => s)
    .join(' + ');

  return `(${cliffordStr}) ⊗ (${z4Str}) ⊗ (${z3Str})`;
}
