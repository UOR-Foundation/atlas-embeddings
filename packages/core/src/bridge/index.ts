/**
 * Bridge Module
 *
 * This module connects the SGA algebraic foundation to the existing
 * 96-class permutation system.
 *
 * Key operations:
 * - lift: Convert class index to SGA rank-1 element
 * - project: Convert SGA rank-1 element back to class index
 * - validate: Verify commutative diagrams (correctness proofs)
 *
 * The fundamental correctness property is:
 *   For all transforms g ∈ {R, D, T, M} and classes c:
 *   project(g_alg(lift(c))) === g_perm(c)
 *
 * @module bridge
 */

// Lift
export { lift, liftAll, liftMultiple } from './lift';

// Project
export { project, isRank1, projectMultiple, projectStrict } from './project';

// Validation
export {
  validateLiftProject,
  validateR,
  validateD,
  validateT,
  validateM,
  validateAll,
  summarizeResults,
} from './validation';

export type { ValidationResult } from './validation';
