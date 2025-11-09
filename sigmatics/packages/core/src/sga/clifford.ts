/**
 * Clifford Algebra Cl₀,₇ Implementation
 *
 * This module implements the 7-dimensional Clifford algebra with signature (0,7).
 * The geometric product satisfies: eᵢeⱼ + eⱼeᵢ = 2δᵢⱼ
 *
 * Key operations:
 * - Geometric product (the fundamental operation)
 * - Involutions (grade involution, reversion, conjugation)
 * - Utilities (basis vectors, projections, etc.)
 */

import type { Cl07Element, Blade } from './types';
import { EPSILON } from './types';

/**
 * Parse a blade string to an array of basis vector indices
 *
 * Examples:
 *   "1" → []
 *   "e1" → [1]
 *   "e1e3" → [1, 3]
 *   "e1e2e3" → [1, 2, 3]
 */
function parseBlade(blade: Blade): number[] {
  if (blade === '1') return [];

  const matches = blade.match(/e(\d)/g);
  if (!matches) return [];

  return matches.map((m) => parseInt(m.substring(1), 10));
}

/**
 * Format an array of indices as a blade string
 *
 * Examples:
 *   [] → "1"
 *   [1] → "e1"
 *   [1, 3] → "e1e3"
 */
function formatBlade(indices: number[]): Blade {
  if (indices.length === 0) return '1';
  return indices.map((i) => `e${i}`).join('');
}

/**
 * Simplify a blade by merging repeated indices
 *
 * Uses the relation eᵢeᵢ = 1 and anticommutation eᵢeⱼ = -eⱼeᵢ (i≠j)
 *
 * Algorithm: Bubble sort with sign tracking
 * - Adjacent equal indices cancel (eᵢeᵢ = 1)
 * - Adjacent swaps introduce a minus sign
 *
 * Returns: [simplified indices, sign]
 */
function simplifyBladeMerge(indices: number[]): [number[], number] {
  let result = [...indices];
  let sign = 1;

  // Bubble sort to bring duplicates together
  let changed = true;
  while (changed) {
    changed = false;
    for (let i = 0; i < result.length - 1; i++) {
      if (result[i] === result[i + 1]) {
        // eᵢeᵢ = 1, so remove both
        result.splice(i, 2);
        changed = true;
        break;
      } else if (result[i] > result[i + 1]) {
        // Swap and flip sign (anticommutation)
        [result[i], result[i + 1]] = [result[i + 1], result[i]];
        sign *= -1;
        changed = true;
      }
    }
  }

  return [result, sign];
}

/**
 * Create a Clifford element from a sparse representation
 *
 * @param grades - Map or record of blade → coefficient
 */
export function createCliffordElement(
  grades: Map<Blade, number> | Record<Blade, number>,
): Cl07Element {
  const map = grades instanceof Map ? grades : new Map(Object.entries(grades));

  // Clean up near-zero coefficients
  const cleaned = new Map<Blade, number>();
  for (const [blade, coeff] of map) {
    if (Math.abs(coeff) >= EPSILON) {
      cleaned.set(blade, coeff);
    }
  }

  return { grades: cleaned };
}

/**
 * Create the identity element (scalar 1)
 */
export function cliffordIdentity(): Cl07Element {
  return createCliffordElement({ '1': 1 });
}

/**
 * Create the zero element
 */
export function cliffordZero(): Cl07Element {
  return createCliffordElement({});
}

/**
 * Create a basis vector eᵢ
 *
 * @param i - Index 1..7
 */
export function basisVector(i: number): Cl07Element {
  if (i < 1 || i > 7) {
    throw new Error(`Basis vector index must be 1..7, got ${i}`);
  }
  return createCliffordElement({ [`e${i}`]: 1 });
}

/**
 * Create a scalar element
 */
export function scalar(value: number): Cl07Element {
  return createCliffordElement({ '1': value });
}

/**
 * Extract the scalar part of a Clifford element
 */
export function scalarPart(a: Cl07Element): number {
  return a.grades.get('1') ?? 0;
}

/**
 * Geometric product of two Clifford elements
 *
 * This is the fundamental operation of the Clifford algebra.
 * It implements the relation: eᵢeⱼ + eⱼeᵢ = 2δᵢⱼ
 *
 * @param a - First element
 * @param b - Second element
 * @returns The geometric product a·b
 */
export function geometricProduct(a: Cl07Element, b: Cl07Element): Cl07Element {
  const result = new Map<Blade, number>();

  for (const [bladeA, coeffA] of a.grades) {
    for (const [bladeB, coeffB] of b.grades) {
      // Parse blades to index arrays
      const indicesA = parseBlade(bladeA);
      const indicesB = parseBlade(bladeB);

      // Merge and simplify using anticommutation rules
      const [merged, sign] = simplifyBladeMerge([...indicesA, ...indicesB]);

      // Format result blade
      const bladeMerged = formatBlade(merged);

      // Accumulate coefficient
      const coeff = coeffA * coeffB * sign;
      result.set(bladeMerged, (result.get(bladeMerged) ?? 0) + coeff);
    }
  }

  return createCliffordElement(result);
}

/**
 * Add two Clifford elements
 */
export function cliffordAdd(a: Cl07Element, b: Cl07Element): Cl07Element {
  const result = new Map<Blade, number>();

  // Add coefficients from a
  for (const [blade, coeff] of a.grades) {
    result.set(blade, coeff);
  }

  // Add coefficients from b
  for (const [blade, coeff] of b.grades) {
    result.set(blade, (result.get(blade) ?? 0) + coeff);
  }

  return createCliffordElement(result);
}

/**
 * Subtract two Clifford elements
 */
export function cliffordSubtract(a: Cl07Element, b: Cl07Element): Cl07Element {
  return cliffordAdd(a, cliffordScale(b, -1));
}

/**
 * Scale a Clifford element by a scalar
 */
export function cliffordScale(a: Cl07Element, s: number): Cl07Element {
  const result = new Map<Blade, number>();

  for (const [blade, coeff] of a.grades) {
    result.set(blade, coeff * s);
  }

  return createCliffordElement(result);
}

/**
 * Negate a Clifford element
 */
export function cliffordNegate(a: Cl07Element): Cl07Element {
  return cliffordScale(a, -1);
}

/**
 * Get the grade (number of basis vectors) of a blade
 */
function bladeGrade(blade: Blade): number {
  if (blade === '1') return 0;
  return parseBlade(blade).length;
}

/**
 * Project to a specific grade
 *
 * @param a - Clifford element
 * @param k - Grade to project onto (0..7)
 */
export function gradeProject(a: Cl07Element, k: number): Cl07Element {
  const result = new Map<Blade, number>();

  for (const [blade, coeff] of a.grades) {
    if (bladeGrade(blade) === k) {
      result.set(blade, coeff);
    }
  }

  return createCliffordElement(result);
}

/**
 * Grade involution: flip sign of odd-grade blades
 *
 * α̂(eᵢ₁eᵢ₂...eᵢₖ) = (-1)^k eᵢ₁eᵢ₂...eᵢₖ
 */
export function gradeInvolution(a: Cl07Element): Cl07Element {
  const result = new Map<Blade, number>();

  for (const [blade, coeff] of a.grades) {
    const grade = bladeGrade(blade);
    const sign = grade % 2 === 0 ? 1 : -1;
    result.set(blade, sign * coeff);
  }

  return createCliffordElement(result);
}

/**
 * Reversion: reverse the order of basis vectors in each blade
 *
 * (eᵢ₁eᵢ₂...eᵢₖ)† = eᵢₖ...eᵢ₂eᵢ₁ = (-1)^(k(k-1)/2) eᵢ₁eᵢ₂...eᵢₖ
 */
export function reversion(a: Cl07Element): Cl07Element {
  const result = new Map<Blade, number>();

  for (const [blade, coeff] of a.grades) {
    const grade = bladeGrade(blade);
    const sign = Math.pow(-1, (grade * (grade - 1)) / 2);
    result.set(blade, sign * coeff);
  }

  return createCliffordElement(result);
}

/**
 * Clifford conjugation: composition of grade involution and reversion
 *
 * x̄ = α̂(x†) = (α̂(x))†
 */
export function cliffordConjugation(a: Cl07Element): Cl07Element {
  return gradeInvolution(reversion(a));
}

/**
 * Test equality of two Clifford elements
 *
 * @param a - First element
 * @param b - Second element
 * @param epsilon - Tolerance for floating-point comparison
 */
export function cliffordEqual(a: Cl07Element, b: Cl07Element, epsilon = EPSILON): boolean {
  // Get all blades from both elements
  const allBlades = new Set([...a.grades.keys(), ...b.grades.keys()]);

  for (const blade of allBlades) {
    const coeffA = a.grades.get(blade) ?? 0;
    const coeffB = b.grades.get(blade) ?? 0;

    if (Math.abs(coeffA - coeffB) >= epsilon) {
      return false;
    }
  }

  return true;
}

/**
 * Inner product of two vectors (grade-1 elements)
 *
 * For vectors u, v: ⟨u,v⟩ = (uv + vu) / 2
 */
export function innerProduct(u: Cl07Element, v: Cl07Element): number {
  const uv = geometricProduct(u, v);
  const vu = geometricProduct(v, u);
  const sum = cliffordAdd(uv, vu);
  const scaled = cliffordScale(sum, 0.5);
  return scalarPart(scaled);
}

/**
 * Get the vector part (grade-1) of a Clifford element
 */
export function vectorPart(a: Cl07Element): Cl07Element {
  return gradeProject(a, 1);
}

/**
 * Count the number of basis vectors in a blade
 */
export function countBasisVectors(blade: Blade): number {
  return bladeGrade(blade);
}
