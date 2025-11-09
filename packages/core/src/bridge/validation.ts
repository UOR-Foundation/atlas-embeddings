/**
 * Bridge Validation
 *
 * This module validates the fundamental correctness property of v0.3.0:
 * the commutative diagrams between SGA transforms and class permutations.
 *
 * For all transforms g ∈ {R, D, T, M} and classes c ∈ [0,95]:
 *
 *   project(g_alg(lift(c))) === g_perm(c)
 *
 * This is THE critical test that proves the SGA implementation correctly
 * implements the class transform semantics.
 */

import type { SgaElement } from '../sga/types';
import {
  transformR,
  transformD,
  transformT,
  transformM,
  transformRPower,
  transformDPower,
  transformTPower,
} from '../sga/transforms';
import { lift } from './lift';
import { project } from './project';
import {
  applyRotation,
  applyTriality,
  applyTwist,
  applyMirror,
  componentsToClassIndex,
  decodeClassIndex,
} from '../class-system/class';

/**
 * Result of a validation test
 */
export interface ValidationResult {
  /** Test name/description */
  name: string;

  /** Class index tested */
  classIndex: number;

  /** Whether test passed */
  passed: boolean;

  /** Expected result */
  expected: number | null;

  /** Actual result */
  actual: number | null;

  /** Error message if failed */
  error?: string;
}

/**
 * Validate lift-project round trip for a single class
 *
 * Tests: project(lift(c)) === c
 */
function validateLiftProjectForClass(classIndex: number): ValidationResult {
  try {
    const lifted = lift(classIndex);
    const projected = project(lifted);

    const passed = projected === classIndex;

    return {
      name: 'lift-project round trip',
      classIndex,
      passed,
      expected: classIndex,
      actual: projected,
      error: passed ? undefined : 'Round trip failed',
    };
  } catch (error) {
    return {
      name: 'lift-project round trip',
      classIndex,
      passed: false,
      expected: classIndex,
      actual: null,
      error: error instanceof Error ? error.message : String(error),
    };
  }
}

/**
 * Validate lift-project round trip for all classes
 */
export function validateLiftProject(): {
  allPassed: boolean;
  results: ValidationResult[];
  summary: { total: number; passed: number; failed: number };
} {
  const results = Array.from({ length: 96 }, (_, i) => validateLiftProjectForClass(i));
  const passed = results.filter((r) => r.passed).length;
  const failed = results.filter((r) => !r.passed).length;

  return {
    allPassed: failed === 0,
    results,
    summary: {
      total: results.length,
      passed,
      failed,
    },
  };
}

/**
 * Validate R transform commutative diagram for a single class
 *
 * Tests: project(R_alg(lift(c))) === R_perm(c)
 */
function validateRForClass(classIndex: number, k: number = 1): ValidationResult {
  try {
    const lifted = lift(classIndex);
    const transformedSGA = transformRPower(lifted, k);
    const projectedBack = project(transformedSGA);

    // Apply R via permutation
    const components = decodeClassIndex(classIndex);
    const transformedComp = applyRotation(components, k);
    const expectedClass = componentsToClassIndex(transformedComp);

    const passed = projectedBack === expectedClass;

    return {
      name: `R^${k} commutative diagram`,
      classIndex,
      passed,
      expected: expectedClass,
      actual: projectedBack,
      error: passed ? undefined : `R^${k} diagram failed`,
    };
  } catch (error) {
    return {
      name: `R^${k} commutative diagram`,
      classIndex,
      passed: false,
      expected: null,
      actual: null,
      error: error instanceof Error ? error.message : String(error),
    };
  }
}

/**
 * Validate R transform for all classes
 */
export function validateR(): {
  allPassed: boolean;
  results: ValidationResult[];
  summary: { total: number; passed: number; failed: number };
} {
  const results: ValidationResult[] = [];

  // Test R^1, R^2, R^3 for all classes
  for (let c = 0; c < 96; c++) {
    for (let k = 1; k <= 3; k++) {
      results.push(validateRForClass(c, k));
    }
  }

  const passed = results.filter((r) => r.passed).length;
  const failed = results.filter((r) => !r.passed).length;

  return {
    allPassed: failed === 0,
    results,
    summary: {
      total: results.length,
      passed,
      failed,
    },
  };
}

/**
 * Validate D transform commutative diagram for a single class
 *
 * Tests: project(D_alg(lift(c))) === D_perm(c)
 */
function validateDForClass(classIndex: number, k: number = 1): ValidationResult {
  try {
    const lifted = lift(classIndex);
    const transformedSGA = transformDPower(lifted, k);
    const projectedBack = project(transformedSGA);

    // Apply D via permutation
    const components = decodeClassIndex(classIndex);
    const transformedComp = applyTriality(components, k);
    const expectedClass = componentsToClassIndex(transformedComp);

    const passed = projectedBack === expectedClass;

    return {
      name: `D^${k} commutative diagram`,
      classIndex,
      passed,
      expected: expectedClass,
      actual: projectedBack,
      error: passed ? undefined : `D^${k} diagram failed`,
    };
  } catch (error) {
    return {
      name: `D^${k} commutative diagram`,
      classIndex,
      passed: false,
      expected: null,
      actual: null,
      error: error instanceof Error ? error.message : String(error),
    };
  }
}

/**
 * Validate D transform for all classes
 */
export function validateD(): {
  allPassed: boolean;
  results: ValidationResult[];
  summary: { total: number; passed: number; failed: number };
} {
  const results: ValidationResult[] = [];

  // Test D^1, D^2 for all classes
  for (let c = 0; c < 96; c++) {
    for (let k = 1; k <= 2; k++) {
      results.push(validateDForClass(c, k));
    }
  }

  const passed = results.filter((r) => r.passed).length;
  const failed = results.filter((r) => !r.passed).length;

  return {
    allPassed: failed === 0,
    results,
    summary: {
      total: results.length,
      passed,
      failed,
    },
  };
}

/**
 * Validate T transform commutative diagram for a single class
 *
 * Tests: project(T_alg(lift(c))) === T_perm(c)
 */
function validateTForClass(classIndex: number, k: number = 1): ValidationResult {
  try {
    const lifted = lift(classIndex);
    const transformedSGA = transformTPower(lifted, k);
    const projectedBack = project(transformedSGA);

    // Apply T via permutation
    const components = decodeClassIndex(classIndex);
    const transformedComp = applyTwist(components, k);
    const expectedClass = componentsToClassIndex(transformedComp);

    const passed = projectedBack === expectedClass;

    return {
      name: `T^${k} commutative diagram`,
      classIndex,
      passed,
      expected: expectedClass,
      actual: projectedBack,
      error: passed ? undefined : `T^${k} diagram failed`,
    };
  } catch (error) {
    return {
      name: `T^${k} commutative diagram`,
      classIndex,
      passed: false,
      expected: null,
      actual: null,
      error: error instanceof Error ? error.message : String(error),
    };
  }
}

/**
 * Validate T transform for all classes
 */
export function validateT(): {
  allPassed: boolean;
  results: ValidationResult[];
  summary: { total: number; passed: number; failed: number };
} {
  const results: ValidationResult[] = [];

  // Test T^1 through T^7 for all classes
  for (let c = 0; c < 96; c++) {
    for (let k = 1; k <= 7; k++) {
      results.push(validateTForClass(c, k));
    }
  }

  const passed = results.filter((r) => r.passed).length;
  const failed = results.filter((r) => !r.passed).length;

  return {
    allPassed: failed === 0,
    results,
    summary: {
      total: results.length,
      passed,
      failed,
    },
  };
}

/**
 * Validate M transform commutative diagram for a single class
 *
 * Tests: project(M_alg(lift(c))) === M_perm(c)
 */
function validateMForClass(classIndex: number): ValidationResult {
  try {
    const lifted = lift(classIndex);
    const transformedSGA = transformM(lifted);
    const projectedBack = project(transformedSGA);

    // Apply M via permutation
    const components = decodeClassIndex(classIndex);
    const transformedComp = applyMirror(components);
    const expectedClass = componentsToClassIndex(transformedComp);

    const passed = projectedBack === expectedClass;

    return {
      name: 'M commutative diagram',
      classIndex,
      passed,
      expected: expectedClass,
      actual: projectedBack,
      error: passed ? undefined : 'M diagram failed',
    };
  } catch (error) {
    return {
      name: 'M commutative diagram',
      classIndex,
      passed: false,
      expected: null,
      actual: null,
      error: error instanceof Error ? error.message : String(error),
    };
  }
}

/**
 * Validate M transform for all classes
 */
export function validateM(): {
  allPassed: boolean;
  results: ValidationResult[];
  summary: { total: number; passed: number; failed: number };
} {
  const results = Array.from({ length: 96 }, (_, i) => validateMForClass(i));
  const passed = results.filter((r) => r.passed).length;
  const failed = results.filter((r) => !r.passed).length;

  return {
    allPassed: failed === 0,
    results,
    summary: {
      total: results.length,
      passed,
      failed,
    },
  };
}

/**
 * Run all validations
 *
 * This is the comprehensive test suite that proves v0.3.0 correctness.
 */
export function validateAll(): {
  allPassed: boolean;
  results: ValidationResult[];
  summary: { total: number; passed: number; failed: number };
} {
  const results: ValidationResult[] = [
    ...validateLiftProject().results,
    ...validateR().results,
    ...validateD().results,
    ...validateT().results,
    ...validateM().results,
  ];

  const passed = results.filter((r) => r.passed).length;
  const failed = results.filter((r) => !r.passed).length;

  return {
    allPassed: failed === 0,
    results,
    summary: {
      total: results.length,
      passed,
      failed,
    },
  };
}

/**
 * Get a summary of validation results
 */
export function summarizeResults(results: ValidationResult[]): string {
  const passed = results.filter((r) => r.passed).length;
  const failed = results.filter((r) => !r.passed).length;
  const total = results.length;

  let summary = `Validation Summary:\n`;
  summary += `  Total:  ${total}\n`;
  summary += `  Passed: ${passed}\n`;
  summary += `  Failed: ${failed}\n`;

  if (failed > 0) {
    summary += `\nFailed tests:\n`;
    for (const result of results.filter((r) => !r.passed)) {
      summary += `  ${result.name} - class ${result.classIndex}: ${result.error}\n`;
      summary += `    Expected: ${result.expected}, Actual: ${result.actual}\n`;
    }
  }

  return summary;
}
