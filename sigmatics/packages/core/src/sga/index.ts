/**
 * Sigmatics Geometric Algebra (SGA)
 *
 * This module provides the complete algebraic foundation for Sigmatics:
 *
 *   SGA = Cl₀,₇ ⊗ ℝ[ℤ₄] ⊗ ℝ[ℤ₃]
 *
 * The SGA serves as the formal foundation beneath the 96-class permutation
 * system, enabling:
 *
 * - Verification of transform correctness via commutative diagrams
 * - Extension to higher-grade elements (bivectors, trivectors)
 * - Geometric semantics via the octonion channel
 * - Complete algebraic automorphism implementations of R/D/T/M
 *
 * @module sga
 */

// Types
export type { SgaElement, Cl07Element, Z4Element, Z3Element, Rank1Basis, Blade } from './types';

export { EPSILON } from './types';

// Clifford Algebra
export {
  createCliffordElement,
  cliffordIdentity,
  cliffordZero,
  basisVector,
  scalar,
  scalarPart,
  geometricProduct,
  cliffordAdd,
  cliffordSubtract,
  cliffordScale,
  cliffordNegate,
  gradeProject,
  gradeInvolution,
  reversion,
  cliffordConjugation,
  cliffordEqual,
  innerProduct as cliffordInnerProduct,
  vectorPart,
  countBasisVectors,
} from './clifford';

// Group Algebras
export {
  // ℝ[ℤ₄]
  z4Identity,
  z4Zero,
  z4Generator,
  z4Power,
  z4Multiply,
  z4Add,
  z4Subtract,
  z4Scale,
  z4Invert,
  extractZ4Power,
  z4Equal,
  // ℝ[ℤ₃]
  z3Identity,
  z3Zero,
  z3Generator,
  z3Power,
  z3Multiply,
  z3Add,
  z3Subtract,
  z3Scale,
  z3Invert,
  extractZ3Power,
  z3Equal,
} from './group-algebras';

// SGA Elements
export {
  createSgaElement,
  sgaIdentity,
  sgaZero,
  createRank1Basis,
  createRank1BasisFromCoords,
  sgaMultiply,
  sgaAdd,
  sgaScale,
  sgaEqual,
  sgaGradeInvolution,
  sgaReversion,
  sgaCliffordConjugation,
  sgaPower,
  sgaIsZero,
  sgaIsIdentity,
  sgaToString,
} from './sga-element';

// Transforms
export {
  transformR,
  transformRPower,
  transformD,
  transformDPower,
  transformT,
  transformTPower,
  transformM,
  verifyR4Identity,
  verifyD3Identity,
  verifyT8Identity,
  verifyM2Identity,
} from './transforms';

// Fano Plane
export {
  FANO_LINES,
  crossProductTable,
  crossProduct,
  verifyFanoPlane,
  getLinesContaining,
  isFanoLine,
} from './fano';

// Octonion Channel
export {
  innerProduct as octonionInnerProduct,
  vectorCrossProduct,
  cayleyProduct,
  octonionConjugate,
  octonionNormSquared,
  octonionNorm,
  verifyAlternativity,
  verifyNormMultiplicativity,
  randomOctonion,
} from './octonion';
