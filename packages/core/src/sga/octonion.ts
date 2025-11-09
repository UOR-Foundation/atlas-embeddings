/**
 * Octonion Channel
 *
 * This module implements the octonion multiplication (Cayley product)
 * on the scalar+vector subspace ℝ ⊕ V ⊂ Cl₀,₇.
 *
 * The Cayley product is:
 *   (α + u) ∘ (β + v) = (αβ - ⟨u,v⟩) + (αv + βu + u×v)
 *
 * where:
 *   α, β are scalars
 *   u, v are vectors in V = span{e₁, ..., e₇}
 *   ⟨·,·⟩ is the Euclidean inner product
 *   × is the cross product defined by the Fano plane
 *
 * The octonions are alternative (not associative), but satisfy:
 *   (xy)y = x(yy)  and  y(yx) = (yy)x  (alternativity)
 *   |xy| = |x| |y|  (norm multiplicative)
 */

import type { Cl07Element, Blade } from './types';
import {
  createCliffordElement,
  scalarPart,
  gradeProject,
  cliffordAdd,
  cliffordScale,
  basisVector,
} from './clifford';
import { crossProduct } from './fano';

/**
 * Extract vector components from a Clifford element
 *
 * @param a - Clifford element (should be grade ≤ 1)
 * @returns Array of 7 coefficients [c₁, c₂, ..., c₇] for basis vectors
 */
function extractVectorComponents(a: Cl07Element): number[] {
  const components = [0, 0, 0, 0, 0, 0, 0];

  const vector = gradeProject(a, 1);

  for (const [blade, coeff] of vector.grades) {
    // Parse blade like "e3" to get index 3
    const match = blade.match(/e(\d)/);
    if (match) {
      const index = parseInt(match[1], 10);
      if (index >= 1 && index <= 7) {
        components[index - 1] = coeff;
      }
    }
  }

  return components;
}

/**
 * Create Clifford element from scalar and vector components
 *
 * @param scalar - Scalar coefficient
 * @param vector - Array of 7 vector coefficients
 */
function createFromComponents(scalar: number, vector: number[]): Cl07Element {
  const grades = new Map<Blade, number>();

  if (Math.abs(scalar) >= 1e-10) {
    grades.set('1', scalar);
  }

  for (let i = 0; i < 7; i++) {
    if (Math.abs(vector[i]) >= 1e-10) {
      grades.set(`e${i + 1}`, vector[i]);
    }
  }

  return createCliffordElement(grades);
}

/**
 * Inner product of two vectors
 *
 * ⟨u,v⟩ = Σᵢ uᵢvᵢ
 *
 * @param u - First vector (grade-1 Clifford element)
 * @param v - Second vector (grade-1 Clifford element)
 */
export function innerProduct(u: Cl07Element, v: Cl07Element): number {
  const uComponents = extractVectorComponents(u);
  const vComponents = extractVectorComponents(v);

  let sum = 0;
  for (let i = 0; i < 7; i++) {
    sum += uComponents[i] * vComponents[i];
  }

  return sum;
}

/**
 * Cross product of two vectors (Fano plane structure)
 *
 * u×v = Σᵢⱼ uᵢvⱼ (eᵢ × eⱼ)
 *
 * @param u - First vector
 * @param v - Second vector
 */
export function vectorCrossProduct(u: Cl07Element, v: Cl07Element): Cl07Element {
  const uComponents = extractVectorComponents(u);
  const vComponents = extractVectorComponents(v);

  const result = [0, 0, 0, 0, 0, 0, 0];

  // Compute cross product using Fano plane
  for (let i = 0; i < 7; i++) {
    for (let j = 0; j < 7; j++) {
      if (i !== j) {
        const { index, sign } = crossProduct(i + 1, j + 1);
        if (index > 0) {
          result[index - 1] += uComponents[i] * vComponents[j] * sign;
        }
      }
    }
  }

  return createFromComponents(0, result);
}

/**
 * Cayley product (octonion multiplication)
 *
 * (α + u) ∘ (β + v) = (αβ - ⟨u,v⟩) + (αv + βu + u×v)
 *
 * This is the fundamental product structure of the octonions.
 * It is alternative but not associative.
 *
 * @param x - First octonion (scalar + vector part)
 * @param y - Second octonion (scalar + vector part)
 */
export function cayleyProduct(x: Cl07Element, y: Cl07Element): Cl07Element {
  // Extract scalar and vector parts
  const alpha = scalarPart(x);
  const beta = scalarPart(y);
  const u = gradeProject(x, 1);
  const v = gradeProject(y, 1);

  // Scalar part: αβ - ⟨u,v⟩
  const scalarPart_ = alpha * beta - innerProduct(u, v);

  // Vector part: αv + βu + u×v
  const alphav = cliffordScale(v, alpha);
  const betau = cliffordScale(u, beta);
  const crossProd = vectorCrossProduct(u, v);

  const vectorPart = cliffordAdd(cliffordAdd(alphav, betau), crossProd);

  // Combine scalar and vector parts
  return createFromComponents(scalarPart_, extractVectorComponents(vectorPart));
}

/**
 * Octonion conjugate
 *
 * (α + u)* = α - u
 *
 * @param x - Octonion
 */
export function octonionConjugate(x: Cl07Element): Cl07Element {
  const alpha = scalarPart(x);
  const u = gradeProject(x, 1);

  return cliffordAdd(createCliffordElement({ '1': alpha }), cliffordScale(u, -1));
}

/**
 * Octonion norm squared
 *
 * |x|² = x* ∘ x = α² + Σᵢ uᵢ²
 *
 * @param x - Octonion
 */
export function octonionNormSquared(x: Cl07Element): number {
  const alpha = scalarPart(x);
  const components = extractVectorComponents(x);

  let sum = alpha * alpha;
  for (const c of components) {
    sum += c * c;
  }

  return sum;
}

/**
 * Octonion norm
 *
 * |x| = √(x* ∘ x)
 *
 * @param x - Octonion
 */
export function octonionNorm(x: Cl07Element): number {
  return Math.sqrt(octonionNormSquared(x));
}

/**
 * Verify alternativity property
 *
 * Checks: (xy)y = x(yy) for given x, y
 *
 * @param x - First octonion
 * @param y - Second octonion
 * @param epsilon - Tolerance for floating-point comparison
 */
export function verifyAlternativity(x: Cl07Element, y: Cl07Element, epsilon = 1e-10): boolean {
  if (!x || typeof x !== 'object' || !x.grades) {
    throw new Error('verifyAlternativity expects a Clifford element (octonion) as first argument');
  }
  if (!y || typeof y !== 'object' || !y.grades) {
    throw new Error('verifyAlternativity expects a Clifford element (octonion) as second argument');
  }

  // Compute (xy)y
  const xy = cayleyProduct(x, y);
  const xy_y = cayleyProduct(xy, y);

  // Compute x(yy)
  const yy = cayleyProduct(y, y);
  const x_yy = cayleyProduct(x, yy);

  // Check if they're equal
  const diff = cliffordAdd(xy_y, cliffordScale(x_yy, -1));

  // Check all coefficients are near zero
  for (const [, coeff] of diff.grades) {
    if (Math.abs(coeff) >= epsilon) {
      return false;
    }
  }

  return true;
}

/**
 * Verify norm multiplicativity
 *
 * Checks: |xy| = |x| |y| for given x, y
 *
 * @param x - First octonion
 * @param y - Second octonion
 * @param epsilon - Tolerance for floating-point comparison
 */
export function verifyNormMultiplicativity(
  x: Cl07Element,
  y: Cl07Element,
  epsilon = 1e-10,
): boolean {
  if (!x || typeof x !== 'object' || !x.grades) {
    throw new Error('verifyNormMultiplicativity expects a Clifford element (octonion) as first argument');
  }
  if (!y || typeof y !== 'object' || !y.grades) {
    throw new Error('verifyNormMultiplicativity expects a Clifford element (octonion) as second argument');
  }

  const xy = cayleyProduct(x, y);

  const normXY = octonionNorm(xy);
  const normX = octonionNorm(x);
  const normY = octonionNorm(y);

  return Math.abs(normXY - normX * normY) < epsilon;
}

/**
 * Create a random octonion for testing
 *
 * @param maxCoeff - Maximum coefficient value
 */
export function randomOctonion(maxCoeff = 1.0): Cl07Element {
  const scalar = (Math.random() - 0.5) * 2 * maxCoeff;
  const vector = Array.from({ length: 7 }, () => (Math.random() - 0.5) * 2 * maxCoeff);

  return createFromComponents(scalar, vector);
}
