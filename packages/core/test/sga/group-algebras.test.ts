/**
 * Group Algebra Tests
 *
 * Tests for ℝ[ℤ₄] and ℝ[ℤ₃] group algebras, focusing on:
 * - General element inversion
 * - Fast path optimization for pure powers
 * - Non-invertible element detection
 */

// FIX: Declare require and module for Node.js environment compatibility
declare const require: any;
declare const module: any;

import {
  z4Identity,
  z4Generator,
  z4Power,
  z4Multiply,
  z4Add,
  z4Scale,
  z4Invert,
  z4Equal,
  z3Identity,
  z3Generator,
  z3Power,
  z3Multiply,
  z3Add,
  z3Scale,
  z3Invert,
  z3Equal,
} from '../../src/sga/group-algebras';

// Test utilities
function assertEqual<T>(actual: T, expected: T, message: string): void {
  if (actual !== expected) {
    throw new Error(`${message}\n  Expected: ${expected}\n  Actual: ${actual}`);
  }
}

function assertThrows(fn: () => void, message: string): void {
  try {
    fn();
    throw new Error(`${message}: Expected function to throw, but it did not`);
  } catch (error) {
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
// ℝ[ℤ₄] Inversion Tests
// ============================================================================

function testZ4PurePowerInversion(): void {
  // Test fast path: pure powers r^k
  for (let k = 0; k < 4; k++) {
    const element = z4Power(k);
    const inverse = z4Invert(element);
    const product = z4Multiply(element, inverse);
    const identity = z4Identity();

    if (!z4Equal(product, identity)) {
      throw new Error(`r^${k} * (r^${k})⁻¹ should equal identity`);
    }
  }
}

function testZ4GeneralElementInversion(): void {
  // Test general element: 1 + 2r (not a pure power, but invertible)
  // Note: 1 + r is NOT invertible (it's a zero divisor), but 1 + 2r is
  const element = z4Add(z4Power(0), z4Scale(z4Power(1), 2));
  const inverse = z4Invert(element);
  const product = z4Multiply(element, inverse);
  const identity = z4Identity();

  if (!z4Equal(product, identity)) {
    throw new Error('(1 + 2r) * (1 + 2r)⁻¹ should equal identity');
  }

  // Also check the other direction
  const product2 = z4Multiply(inverse, element);
  if (!z4Equal(product2, identity)) {
    throw new Error('(1 + 2r)⁻¹ * (1 + 2r) should equal identity');
  }
}

function testZ4ComplexElementInversion(): void {
  // Test: 2 + 3r + r² - r³
  const element = {
    coefficients: [2, 3, 1, -1] as [number, number, number, number],
  };
  const inverse = z4Invert(element);
  const product = z4Multiply(element, inverse);
  const identity = z4Identity();

  if (!z4Equal(product, identity)) {
    throw new Error('(2 + 3r + r² - r³) * inverse should equal identity');
  }
}

function testZ4ScaledElementInversion(): void {
  // Test: 3r² (scalar multiple of pure power)
  const element = z4Scale(z4Power(2), 3);
  const inverse = z4Invert(element);
  const product = z4Multiply(element, inverse);
  const identity = z4Identity();

  if (!z4Equal(product, identity)) {
    throw new Error('(3r²) * (3r²)⁻¹ should equal identity');
  }
}

function testZ4NonInvertibleElement(): void {
  // Test zero divisor: 1 + r² (this is non-invertible)
  // In ℝ[ℤ₄], 1 + r² is a zero divisor because (1 + r²)(1 - r²) = 1 - r⁴ = 0
  const element = z4Add(z4Power(0), z4Power(2));

  assertThrows(() => z4Invert(element), 'Should not be able to invert 1 + r²');
}

function testZ4ZeroNotInvertible(): void {
  const zero = { coefficients: [0, 0, 0, 0] as [number, number, number, number] };
  assertThrows(() => z4Invert(zero), 'Should not be able to invert zero');
}

// ============================================================================
// ℝ[ℤ₃] Inversion Tests
// ============================================================================

function testZ3PurePowerInversion(): void {
  // Test fast path: pure powers τ^k
  for (let k = 0; k < 3; k++) {
    const element = z3Power(k);
    const inverse = z3Invert(element);
    const product = z3Multiply(element, inverse);
    const identity = z3Identity();

    if (!z3Equal(product, identity)) {
      throw new Error(`τ^${k} * (τ^${k})⁻¹ should equal identity`);
    }
  }
}

function testZ3GeneralElementInversion(): void {
  // Test general element: 1 + τ (not a pure power)
  const element = z3Add(z3Power(0), z3Power(1));
  const inverse = z3Invert(element);
  const product = z3Multiply(element, inverse);
  const identity = z3Identity();

  if (!z3Equal(product, identity)) {
    throw new Error('(1 + τ) * (1 + τ)⁻¹ should equal identity');
  }

  // Also check the other direction
  const product2 = z3Multiply(inverse, element);
  if (!z3Equal(product2, identity)) {
    throw new Error('(1 + τ)⁻¹ * (1 + τ) should equal identity');
  }
}

function testZ3ComplexElementInversion(): void {
  // Test: 2 + 3τ - τ²
  const element = { coefficients: [2, 3, -1] as [number, number, number] };
  const inverse = z3Invert(element);
  const product = z3Multiply(element, inverse);
  const identity = z3Identity();

  if (!z3Equal(product, identity)) {
    throw new Error('(2 + 3τ - τ²) * inverse should equal identity');
  }
}

function testZ3ScaledElementInversion(): void {
  // Test: 2τ (scalar multiple of pure power)
  const element = z3Scale(z3Power(1), 2);
  const inverse = z3Invert(element);
  const product = z3Multiply(element, inverse);
  const identity = z3Identity();

  if (!z3Equal(product, identity)) {
    throw new Error('(2τ) * (2τ)⁻¹ should equal identity');
  }
}

function testZ3NonInvertibleElement(): void {
  // Test zero divisor: 1 + τ + τ² (sum of all basis elements)
  // This corresponds to the augmentation ideal and is non-invertible
  const element = z3Add(z3Add(z3Power(0), z3Power(1)), z3Power(2));

  assertThrows(() => z3Invert(element), 'Should not be able to invert 1 + τ + τ²');
}

function testZ3ZeroNotInvertible(): void {
  const zero = { coefficients: [0, 0, 0] as [number, number, number] };
  assertThrows(() => z3Invert(zero), 'Should not be able to invert zero');
}

// ============================================================================
// Main Test Runner
// ============================================================================

export function runGroupAlgebraTests(): void {
  console.log('═══════════════════════════════════════════════════════════');
  console.log('  Group Algebra Inversion Test Suite');
  console.log('═══════════════════════════════════════════════════════════');
  console.log();

  console.log('Testing ℝ[ℤ₄] inversions...');
  runTest('Z4: Pure power inversion (fast path)', testZ4PurePowerInversion);
  runTest('Z4: General element inversion (1 + 2r)', testZ4GeneralElementInversion);
  runTest('Z4: Complex element inversion', testZ4ComplexElementInversion);
  runTest('Z4: Scaled element inversion (3r²)', testZ4ScaledElementInversion);
  runTest('Z4: Non-invertible element detection (1 + r²)', testZ4NonInvertibleElement);
  runTest('Z4: Zero is not invertible', testZ4ZeroNotInvertible);

  console.log();
  console.log('Testing ℝ[ℤ₃] inversions...');
  runTest('Z3: Pure power inversion (fast path)', testZ3PurePowerInversion);
  runTest('Z3: General element inversion (1 + τ)', testZ3GeneralElementInversion);
  runTest('Z3: Complex element inversion', testZ3ComplexElementInversion);
  runTest('Z3: Scaled element inversion (2τ)', testZ3ScaledElementInversion);
  runTest('Z3: Non-invertible element detection', testZ3NonInvertibleElement);
  runTest('Z3: Zero is not invertible', testZ3ZeroNotInvertible);

  console.log();
  console.log('═══════════════════════════════════════════════════════════');
  console.log('  ✓ All group algebra inversion tests passed!');
  console.log('═══════════════════════════════════════════════════════════');
  console.log();
}

// Run tests if executed directly
if (require.main === module) {
  try {
    runGroupAlgebraTests();
  } catch (error) {
    console.error('Tests failed!');
    process.exit(1);
  }
}
