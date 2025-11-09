/**
 * Group Algebras ℝ[ℤ₄] and ℝ[ℤ₃]
 *
 * This module implements the real group algebras for:
 * - ℤ₄: cyclic group of order 4 (generator r)
 * - ℤ₃: cyclic group of order 3 (generator τ)
 *
 * These algebras capture the quadrant rotation (R) and triality (D) structure.
 */

import type { Z4Element, Z3Element } from './types';
import { EPSILON } from './types';

// ============================================================================
// ℝ[ℤ₄] - Real Group Algebra of Cyclic Order-4 Group
// ============================================================================

/**
 * Create the identity element in ℝ[ℤ₄]
 *
 * r⁰ = [1, 0, 0, 0]
 */
export function z4Identity(): Z4Element {
  return { coefficients: [1, 0, 0, 0] };
}

/**
 * Create the zero element in ℝ[ℤ₄]
 */
export function z4Zero(): Z4Element {
  return { coefficients: [0, 0, 0, 0] };
}

/**
 * Create the generator r in ℝ[ℤ₄]
 *
 * r¹ = [0, 1, 0, 0]
 */
export function z4Generator(): Z4Element {
  return { coefficients: [0, 1, 0, 0] };
}

/**
 * Create r^k for k ∈ {0, 1, 2, 3}
 *
 * @param k - Power of r (will be reduced mod 4)
 */
export function z4Power(k: number): Z4Element {
  if (typeof k !== 'number' || !Number.isFinite(k)) {
    throw new Error(`z4Power expects a finite number, got: ${typeof k}`);
  }

  const index = ((k % 4) + 4) % 4; // Ensure positive
  const coefficients: [number, number, number, number] = [0, 0, 0, 0];
  coefficients[index] = 1;
  return { coefficients };
}

/**
 * Multiply two elements of ℝ[ℤ₄]
 *
 * Uses convolution: (Σ aᵢrⁱ)(Σ bⱼrʲ) = Σ (Σ aᵢbⱼ) r^(i+j)
 *
 * @param a - First element
 * @param b - Second element
 */
export function z4Multiply(a: Z4Element, b: Z4Element): Z4Element {
  const result: [number, number, number, number] = [0, 0, 0, 0];

  for (let i = 0; i < 4; i++) {
    for (let j = 0; j < 4; j++) {
      const k = (i + j) % 4;
      result[k] += a.coefficients[i] * b.coefficients[j];
    }
  }

  return { coefficients: result };
}

/**
 * Add two elements of ℝ[ℤ₄]
 */
export function z4Add(a: Z4Element, b: Z4Element): Z4Element {
  return {
    coefficients: [
      a.coefficients[0] + b.coefficients[0],
      a.coefficients[1] + b.coefficients[1],
      a.coefficients[2] + b.coefficients[2],
      a.coefficients[3] + b.coefficients[3],
    ],
  };
}

/**
 * Subtract two elements of ℝ[ℤ₄]
 */
export function z4Subtract(a: Z4Element, b: Z4Element): Z4Element {
  return {
    coefficients: [
      a.coefficients[0] - b.coefficients[0],
      a.coefficients[1] - b.coefficients[1],
      a.coefficients[2] - b.coefficients[2],
      a.coefficients[3] - b.coefficients[3],
    ],
  };
}

/**
 * Scale an element of ℝ[ℤ₄] by a real scalar
 */
export function z4Scale(a: Z4Element, scalar: number): Z4Element {
  return {
    coefficients: [
      a.coefficients[0] * scalar,
      a.coefficients[1] * scalar,
      a.coefficients[2] * scalar,
      a.coefficients[3] * scalar,
    ],
  };
}

/**
 * Solve a 4×4 linear system using Gaussian elimination
 * Returns null if the system is singular (no unique solution)
 */
function solveLinearSystem4x4(
  matrix: number[][],
  rhs: number[],
): [number, number, number, number] | null {
  // Create augmented matrix [A|b]
  const aug: number[][] = matrix.map((row, i) => [...row, rhs[i]]);

  // Forward elimination
  for (let col = 0; col < 4; col++) {
    // Find pivot
    let maxRow = col;
    for (let row = col + 1; row < 4; row++) {
      if (Math.abs(aug[row][col]) > Math.abs(aug[maxRow][col])) {
        maxRow = row;
      }
    }

    // Check for singularity
    if (Math.abs(aug[maxRow][col]) < EPSILON) {
      return null; // Matrix is singular
    }

    // Swap rows
    [aug[col], aug[maxRow]] = [aug[maxRow], aug[col]];

    // Eliminate column
    for (let row = col + 1; row < 4; row++) {
      const factor = aug[row][col] / aug[col][col];
      for (let j = col; j < 5; j++) {
        aug[row][j] -= factor * aug[col][j];
      }
    }
  }

  // Back substitution
  const solution: number[] = [0, 0, 0, 0];
  for (let i = 3; i >= 0; i--) {
    let sum = aug[i][4];
    for (let j = i + 1; j < 4; j++) {
      sum -= aug[i][j] * solution[j];
    }
    solution[i] = sum / aug[i][i];
  }

  return solution as [number, number, number, number];
}

/**
 * Invert an element in ℝ[ℤ₄]
 *
 * For pure powers r^k, uses fast path: r^k → r^(-k) = r^(4-k)
 * For general elements, solves the linear system ab = 1
 *
 * An element a = a₀ + a₁r + a₂r² + a₃r³ is invertible if and only if
 * the circulant matrix corresponding to multiplication by a is invertible.
 */
export function z4Invert(a: Z4Element): Z4Element {
  // Fast path: check if this is a pure power
  const purePower = extractZ4Power(a);
  if (purePower !== null) {
    // r^k → r^(-k) = r^(4-k)
    return z4Power((4 - purePower) % 4);
  }

  // General case: solve the linear system
  // Multiplication by a = [a₀, a₁, a₂, a₃] gives the circulant matrix:
  // [a₀ a₃ a₂ a₁]
  // [a₁ a₀ a₃ a₂]
  // [a₂ a₁ a₀ a₃]
  // [a₃ a₂ a₁ a₀]
  const [a0, a1, a2, a3] = a.coefficients;
  const matrix = [
    [a0, a3, a2, a1],
    [a1, a0, a3, a2],
    [a2, a1, a0, a3],
    [a3, a2, a1, a0],
  ];

  const rhs = [1, 0, 0, 0]; // We want ab = 1 (identity)

  const solution = solveLinearSystem4x4(matrix, rhs);

  if (solution === null) {
    throw new Error('Element is not invertible in ℝ[ℤ₄]');
  }

  return { coefficients: solution };
}

/**
 * Extract the power k if element is r^k, otherwise return null
 */
export function extractZ4Power(a: Z4Element): number | null {
  // Check which coefficient is 1
  for (let i = 0; i < 4; i++) {
    if (Math.abs(a.coefficients[i] - 1) < EPSILON) {
      // Check that all others are 0
      const allOthersZero = a.coefficients.every((c, j) => i === j || Math.abs(c) < EPSILON);
      if (allOthersZero) return i;
    }
  }
  return null;
}

/**
 * Test equality of two ℝ[ℤ₄] elements
 */
export function z4Equal(a: Z4Element, b: Z4Element, epsilon = EPSILON): boolean {
  return a.coefficients.every((c, i) => Math.abs(c - b.coefficients[i]) < epsilon);
}

// ============================================================================
// ℝ[ℤ₃] - Real Group Algebra of Cyclic Order-3 Group
// ============================================================================

/**
 * Create the identity element in ℝ[ℤ₃]
 *
 * τ⁰ = [1, 0, 0]
 */
export function z3Identity(): Z3Element {
  return { coefficients: [1, 0, 0] };
}

/**
 * Create the zero element in ℝ[ℤ₃]
 */
export function z3Zero(): Z3Element {
  return { coefficients: [0, 0, 0] };
}

/**
 * Create the generator τ in ℝ[ℤ₃]
 *
 * τ¹ = [0, 1, 0]
 */
export function z3Generator(): Z3Element {
  return { coefficients: [0, 1, 0] };
}

/**
 * Create τ^k for k ∈ {0, 1, 2}
 *
 * @param k - Power of τ (will be reduced mod 3)
 */
export function z3Power(k: number): Z3Element {
  if (typeof k !== 'number' || !Number.isFinite(k)) {
    throw new Error(`z3Power expects a finite number, got: ${typeof k}`);
  }

  const index = ((k % 3) + 3) % 3; // Ensure positive
  const coefficients: [number, number, number] = [0, 0, 0];
  coefficients[index] = 1;
  return { coefficients };
}

/**
 * Multiply two elements of ℝ[ℤ₃]
 *
 * Uses convolution: (Σ aᵢτⁱ)(Σ bⱼτʲ) = Σ (Σ aᵢbⱼ) τ^(i+j)
 *
 * @param a - First element
 * @param b - Second element
 */
export function z3Multiply(a: Z3Element, b: Z3Element): Z3Element {
  const result: [number, number, number] = [0, 0, 0];

  for (let i = 0; i < 3; i++) {
    for (let j = 0; j < 3; j++) {
      const k = (i + j) % 3;
      result[k] += a.coefficients[i] * b.coefficients[j];
    }
  }

  return { coefficients: result };
}

/**
 * Add two elements of ℝ[ℤ₃]
 */
export function z3Add(a: Z3Element, b: Z3Element): Z3Element {
  return {
    coefficients: [
      a.coefficients[0] + b.coefficients[0],
      a.coefficients[1] + b.coefficients[1],
      a.coefficients[2] + b.coefficients[2],
    ],
  };
}

/**
 * Subtract two elements of ℝ[ℤ₃]
 */
export function z3Subtract(a: Z3Element, b: Z3Element): Z3Element {
  return {
    coefficients: [
      a.coefficients[0] - b.coefficients[0],
      a.coefficients[1] - b.coefficients[1],
      a.coefficients[2] - b.coefficients[2],
    ],
  };
}

/**
 * Scale an element of ℝ[ℤ₃] by a real scalar
 */
export function z3Scale(a: Z3Element, scalar: number): Z3Element {
  return {
    coefficients: [
      a.coefficients[0] * scalar,
      a.coefficients[1] * scalar,
      a.coefficients[2] * scalar,
    ],
  };
}

/**
 * Solve a 3×3 linear system using Gaussian elimination
 * Returns null if the system is singular (no unique solution)
 */
function solveLinearSystem3x3(matrix: number[][], rhs: number[]): [number, number, number] | null {
  // Create augmented matrix [A|b]
  const aug: number[][] = matrix.map((row, i) => [...row, rhs[i]]);

  // Forward elimination
  for (let col = 0; col < 3; col++) {
    // Find pivot
    let maxRow = col;
    for (let row = col + 1; row < 3; row++) {
      if (Math.abs(aug[row][col]) > Math.abs(aug[maxRow][col])) {
        maxRow = row;
      }
    }

    // Check for singularity
    if (Math.abs(aug[maxRow][col]) < EPSILON) {
      return null; // Matrix is singular
    }

    // Swap rows
    [aug[col], aug[maxRow]] = [aug[maxRow], aug[col]];

    // Eliminate column
    for (let row = col + 1; row < 3; row++) {
      const factor = aug[row][col] / aug[col][col];
      for (let j = col; j < 4; j++) {
        aug[row][j] -= factor * aug[col][j];
      }
    }
  }

  // Back substitution
  const solution: number[] = [0, 0, 0];
  for (let i = 2; i >= 0; i--) {
    let sum = aug[i][3];
    for (let j = i + 1; j < 3; j++) {
      sum -= aug[i][j] * solution[j];
    }
    solution[i] = sum / aug[i][i];
  }

  return solution as [number, number, number];
}

/**
 * Invert an element in ℝ[ℤ₃]
 *
 * For pure powers τ^k, uses fast path: τ^k → τ^(-k) = τ^(3-k)
 * For general elements, solves the linear system ab = 1
 *
 * An element a = a₀ + a₁τ + a₂τ² is invertible if and only if
 * the circulant matrix corresponding to multiplication by a is invertible.
 */
export function z3Invert(a: Z3Element): Z3Element {
  // Fast path: check if this is a pure power
  const purePower = extractZ3Power(a);
  if (purePower !== null) {
    // τ^k → τ^(-k) = τ^(3-k)
    return z3Power((3 - purePower) % 3);
  }

  // General case: solve the linear system
  // Multiplication by a = [a₀, a₁, a₂] gives the circulant matrix:
  // [a₀ a₂ a₁]
  // [a₁ a₀ a₂]
  // [a₂ a₁ a₀]
  const [a0, a1, a2] = a.coefficients;
  const matrix = [
    [a0, a2, a1],
    [a1, a0, a2],
    [a2, a1, a0],
  ];

  const rhs = [1, 0, 0]; // We want ab = 1 (identity)

  const solution = solveLinearSystem3x3(matrix, rhs);

  if (solution === null) {
    throw new Error('Element is not invertible in ℝ[ℤ₃]');
  }

  return { coefficients: solution };
}

/**
 * Extract the power k if element is τ^k, otherwise return null
 */
export function extractZ3Power(a: Z3Element): number | null {
  // Check which coefficient is 1
  for (let i = 0; i < 3; i++) {
    if (Math.abs(a.coefficients[i] - 1) < EPSILON) {
      // Check that all others are 0
      const allOthersZero = a.coefficients.every((c, j) => i === j || Math.abs(c) < EPSILON);
      if (allOthersZero) return i;
    }
  }
  return null;
}

/**
 * Test equality of two ℝ[ℤ₃] elements
 */
export function z3Equal(a: Z3Element, b: Z3Element, epsilon = EPSILON): boolean {
  return a.coefficients.every((c, i) => Math.abs(c - b.coefficients[i]) < epsilon);
}
