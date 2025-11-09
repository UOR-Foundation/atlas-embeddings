/**
 * Bug Fix Verification Tests
 *
 * Tests for the bug fixes implemented in v0.3.1
 */

// FIX: Declare require and module for Node.js environment compatibility
declare const require: any;
declare const module: any;

import {
  z4Power,
  z3Power,
  z4Generator,
  z3Generator,
  z4Multiply,
  z3Multiply,
} from '../../src/sga/group-algebras';
import { validateR, validateD, validateT, validateM } from '../../src/bridge/validation';
import { Atlas } from '../../src/api';

// Test utilities
function assertEqual<T>(actual: T, expected: T, message: string): void {
  if (JSON.stringify(actual) !== JSON.stringify(expected)) {
    throw new Error(`${message}\n  Expected: ${JSON.stringify(expected)}\n  Actual: ${JSON.stringify(actual)}`);
  }
}

function assertThrows(fn: () => void, expectedMessage: string | null = null): void {
  try {
    fn();
    throw new Error('Expected function to throw, but it did not');
  } catch (error: any) {
    if (expectedMessage && !error.message.includes(expectedMessage)) {
      throw new Error(`Expected error message to contain "${expectedMessage}", but got: ${error.message}`);
    }
    // Expected to throw, test passes
  }
}

function runTest(name: string, fn: () => void): void {
  try {
    fn();
    console.log(`✓ ${name}`);
  } catch (error: any) {
    console.error(`✗ ${name}`);
    console.error(`  ${error.message}`);
    throw error;
  }
}

// ============================================================================
// BUG-001 & BUG-004: Input Validation for z4Power and z3Power
// ============================================================================

function testZ4PowerInputValidation(): void {
  // Should accept valid numbers
  const r0 = z4Power(0);
  assertEqual(r0.coefficients, [1, 0, 0, 0], 'z4Power(0) should return identity');

  const r4 = z4Power(4);
  assertEqual(r4.coefficients, [1, 0, 0, 0], 'z4Power(4) should wrap to identity');

  // Should reject non-numeric input
  assertThrows(() => z4Power(z4Generator() as any), 'expects a finite number');
  assertThrows(() => z4Power(NaN), 'expects a finite number');
  assertThrows(() => z4Power(Infinity), 'expects a finite number');
  assertThrows(() => z4Power(undefined as any), 'expects a finite number');
  assertThrows(() => z4Power(null as any), 'expects a finite number');
  assertThrows(() => z4Power('5' as any), 'expects a finite number');
}

function testZ3PowerInputValidation(): void {
  // Should accept valid numbers
  const tau0 = z3Power(0);
  assertEqual(tau0.coefficients, [1, 0, 0], 'z3Power(0) should return identity');

  const tau3 = z3Power(3);
  assertEqual(tau3.coefficients, [1, 0, 0], 'z3Power(3) should wrap to identity');

  // Should reject non-numeric input
  assertThrows(() => z3Power(z3Generator() as any), 'expects a finite number');
  assertThrows(() => z3Power(NaN), 'expects a finite number');
  assertThrows(() => z3Power(Infinity), 'expects a finite number');
  assertThrows(() => z3Power(undefined as any), 'expects a finite number');
  assertThrows(() => z3Power(null as any), 'expects a finite number');
  assertThrows(() => z3Power('3' as any), 'expects a finite number');
}

function testZ4PowerWrapAround(): void {
  // Verify that z4^4 = identity through multiplication
  let gen = z4Generator();
  gen = z4Multiply(gen, z4Generator());
  gen = z4Multiply(gen, z4Generator());
  gen = z4Multiply(gen, z4Generator());
  assertEqual(gen.coefficients, [1, 0, 0, 0], 'gen^4 should equal identity');
}

function testZ3PowerWrapAround(): void {
  // Verify that z3^3 = identity through multiplication
  let gen = z3Generator();
  gen = z3Multiply(gen, z3Generator());
  gen = z3Multiply(gen, z3Generator());
  assertEqual(gen.coefficients, [1, 0, 0], 'gen^3 should equal identity');
}

// ============================================================================
// BUG-015: Transform Input Validation
// ============================================================================

function testTransformInputValidation(): void {
  const element = Atlas.SGA.lift(21);

  // Should work with valid SGA element
  Atlas.SGA.R(element);
  Atlas.SGA.D(element);
  Atlas.SGA.T(element);
  Atlas.SGA.M(element);

  // Should reject invalid input
  assertThrows(() => Atlas.SGA.R(1 as any), 'expects an SGA element');
  assertThrows(() => Atlas.SGA.D('hello' as any), 'expects an SGA element');
  assertThrows(() => Atlas.SGA.T(null as any), 'expects an SGA element');
  assertThrows(() => Atlas.SGA.M(undefined as any), 'expects an SGA element');
  assertThrows(() => Atlas.SGA.R({ not: 'sga' } as any), 'expects an SGA element');
}

// ============================================================================
// BUG-009: Validation API Consistency
// ============================================================================

function testValidationAPIConsistency(): void {
  // All validation functions should return structured objects
  const rValidation = validateR();
  if (!rValidation.allPassed || !rValidation.results || !rValidation.summary) {
    throw new Error('validateR should return structured object with allPassed, results, and summary');
  }
  assertEqual(typeof rValidation.allPassed, 'boolean', 'allPassed should be boolean');
  assertEqual(Array.isArray(rValidation.results), true, 'results should be array');
  assertEqual(typeof rValidation.summary.total, 'number', 'summary.total should be number');

  const dValidation = validateD();
  if (!dValidation.allPassed || !dValidation.results || !dValidation.summary) {
    throw new Error('validateD should return structured object');
  }

  const tValidation = validateT();
  if (!tValidation.allPassed || !tValidation.results || !tValidation.summary) {
    throw new Error('validateT should return structured object');
  }

  const mValidation = validateM();
  if (!mValidation.allPassed || !mValidation.results || !mValidation.summary) {
    throw new Error('validateM should return structured object');
  }
}

// ============================================================================
// BUG-012 & BUG-013: Octonion Input Validation
// ============================================================================

function testOctonionInputValidation(): void {
  const x = Atlas.SGA.Octonion.randomOctonion();
  const y = Atlas.SGA.Octonion.randomOctonion();

  // Should work with valid Clifford elements
  Atlas.SGA.Octonion.verifyAlternativity(x, y);
  Atlas.SGA.Octonion.verifyNormMultiplicativity(x, y);

  // Should reject invalid input
  assertThrows(() => Atlas.SGA.Octonion.verifyAlternativity(1 as any, y), 'expects a Clifford element');
  assertThrows(() => Atlas.SGA.Octonion.verifyAlternativity(x, 'invalid' as any), 'expects a Clifford element');
  assertThrows(() => Atlas.SGA.Octonion.verifyAlternativity(null as any, y), 'expects a Clifford element');
  assertThrows(() => Atlas.SGA.Octonion.verifyAlternativity(x, undefined as any), 'expects a Clifford element');

  assertThrows(() => Atlas.SGA.Octonion.verifyNormMultiplicativity(1 as any, y), 'expects a Clifford element');
  assertThrows(() => Atlas.SGA.Octonion.verifyNormMultiplicativity(x, 'invalid' as any), 'expects a Clifford element');
  assertThrows(() => Atlas.SGA.Octonion.verifyNormMultiplicativity(null as any, y), 'expects a Clifford element');
  assertThrows(() => Atlas.SGA.Octonion.verifyNormMultiplicativity(x, undefined as any), 'expects a Clifford element');
}

// ============================================================================
// Main Test Runner
// ============================================================================

export function runBugFixTests(): void {
  console.log('═══════════════════════════════════════════════════════════');
  console.log('  Bug Fix Verification Test Suite (v0.3.1)');
  console.log('═══════════════════════════════════════════════════════════');
  console.log();

  console.log('Testing BUG-001 & BUG-004: Group algebra power input validation...');
  runTest('BUG-001: z4Power input validation', testZ4PowerInputValidation);
  runTest('BUG-004: z3Power input validation', testZ3PowerInputValidation);
  runTest('BUG-001: z4 power wrap-around verification', testZ4PowerWrapAround);
  runTest('BUG-004: z3 power wrap-around verification', testZ3PowerWrapAround);

  console.log();
  console.log('Testing BUG-015: Transform input validation...');
  runTest('BUG-015: Transform input validation', testTransformInputValidation);

  console.log();
  console.log('Testing BUG-009: Validation API consistency...');
  runTest('BUG-009: Validation API returns structured objects', testValidationAPIConsistency);

  console.log();
  console.log('Testing BUG-012 & BUG-013: Octonion input validation...');
  runTest('BUG-012 & BUG-013: Octonion verification input validation', testOctonionInputValidation);

  console.log();
  console.log('═══════════════════════════════════════════════════════════');
  console.log('  ✓ All bug fix tests passed!');
  console.log('═══════════════════════════════════════════════════════════');
  console.log();
}

// Run tests if executed directly
if (require.main === module) {
  try {
    runBugFixTests();
  } catch (error) {
    console.error('Tests failed!');
    process.exit(1);
  }
}
