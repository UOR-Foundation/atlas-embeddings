/**
 * Core type definitions for Sigmatics Geometric Algebra (SGA)
 *
 * SGA = Cl₀,₇ ⊗ ℝ[ℤ₄] ⊗ ℝ[ℤ₃]
 *
 * This module defines the fundamental types for the algebraic foundation
 * of Sigmatics' 96-class system.
 */

/**
 * Blade in Clifford algebra Cl₀,₇
 *
 * A blade is a product of basis vectors e₁, e₂, ..., e₇
 * Examples: "1" (scalar), "e1", "e2", "e1e2", "e1e2e3", etc.
 *
 * Convention: blades are stored as sorted indices (e.g., "e1e3" not "e3e1")
 */
export type Blade = string;

/**
 * Multivector in Clifford algebra Cl₀,₇
 *
 * A multivector is a linear combination of blades.
 * Stored as a sparse map: blade → coefficient
 */
export interface Cl07Element {
  /** Map from blade to coefficient */
  grades: Map<Blade, number>;
}

/**
 * Element of the group algebra ℝ[ℤ₄]
 *
 * Basis: {r⁰, r¹, r², r³}
 * Product: rⁱ · rʲ = r^{(i+j) mod 4}
 */
export interface Z4Element {
  /** Coefficients [r⁰, r¹, r², r³] */
  coefficients: [number, number, number, number];
}

/**
 * Element of the group algebra ℝ[ℤ₃]
 *
 * Basis: {τ⁰, τ¹, τ²}
 * Product: τⁱ · τʲ = τ^{(i+j) mod 3}
 */
export interface Z3Element {
  /** Coefficients [τ⁰, τ¹, τ²] */
  coefficients: [number, number, number];
}

/**
 * Complete SGA element
 *
 * An element of SGA = Cl₀,₇ ⊗ ℝ[ℤ₄] ⊗ ℝ[ℤ₃]
 *
 * The product is the tensor product of the three algebra products.
 */
export interface SgaElement {
  /** Clifford algebra component */
  clifford: Cl07Element;

  /** ℝ[ℤ₄] component (quadrant/scope) */
  z4: Z4Element;

  /** ℝ[ℤ₃] component (modality/triality) */
  z3: Z3Element;
}

/**
 * Rank-1 basis element coordinates
 *
 * Each of the 96 classes corresponds to a rank-1 basis element:
 * E_{h,d,ℓ} = r^h ⊗ e_ℓ ⊗ τ^d
 *
 * where:
 *   h ∈ ℤ₄   (quadrant/scope)
 *   d ∈ ℤ₃   (modality/triality)
 *   ℓ ∈ ℤ₈   (context slot, with e₀ ≡ 1)
 */
export interface Rank1Basis {
  /** Quadrant index (ℤ₄) */
  h: 0 | 1 | 2 | 3;

  /** Modality/triality index (ℤ₃) */
  d: 0 | 1 | 2;

  /** Context slot (ℤ₈, where 0 represents the scalar) */
  l: 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7;
}

/**
 * Tolerance for floating-point comparisons
 */
export const EPSILON = 1e-10;
