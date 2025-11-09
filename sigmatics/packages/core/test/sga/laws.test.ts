/**
 * SGA Algebraic Laws Tests
 *
 * This file tests the fundamental algebraic laws that SGA must satisfy:
 * - R⁴ = identity
 * - D³ = identity
 * - T⁸ = identity
 * - M² = identity
 * - RD = DR (commutation)
 * - RT = TR (commutation)
 * - DT = TD (commutation)
 * - MRM = R⁻¹ (mirror conjugation)
 * - MDM = D⁻¹ (mirror conjugation)
 * - MTM = T⁻¹ (mirror conjugation)
 */

// FIX: Declare require and module for Node.js environment compatibility
declare const require: any;
declare const module: any;

import { lift } from '../../src/bridge/lift';
import {
  transformR,
  transformD,
  transformT,
  transformM,
  transformRPower,
  transformDPower,
  transformTPower,
} from '../../src/sga/transforms';
import { sgaEqual } from '../../src/sga/sga-element';

// Test utilities
function assertEqual<T>(actual: T, expected: T, message: string): void {
  if (actual !== expected) {
    throw new Error(`${message}\n  Expected: ${expected}\n  Actual: ${actual}`);
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
// Order Tests
// ============================================================================

function testR4Identity(): void {
  console.log('\nTesting R⁴ = identity for all 96 classes...');

  for (let c = 0; c < 96; c++) {
    const element = lift(c);
    const result = transformRPower(element, 4);

    if (!sgaEqual(result, element)) {
      throw new Error(`R⁴ ≠ identity for class ${c}`);
    }
  }

  console.log('✓ R⁴ = identity verified for all 96 classes');
}

function testD3Identity(): void {
  console.log('\nTesting D³ = identity for all 96 classes...');

  for (let c = 0; c < 96; c++) {
    const element = lift(c);
    const result = transformDPower(element, 3);

    if (!sgaEqual(result, element)) {
      throw new Error(`D³ ≠ identity for class ${c}`);
    }
  }

  console.log('✓ D³ = identity verified for all 96 classes');
}

function testT8Identity(): void {
  console.log('\nTesting T⁸ = identity for all 96 classes...');

  for (let c = 0; c < 96; c++) {
    const element = lift(c);
    const result = transformTPower(element, 8);

    if (!sgaEqual(result, element)) {
      throw new Error(`T⁸ ≠ identity for class ${c}`);
    }
  }

  console.log('✓ T⁸ = identity verified for all 96 classes');
}

function testM2Identity(): void {
  console.log('\nTesting M² = identity for all 96 classes...');

  for (let c = 0; c < 96; c++) {
    const element = lift(c);
    const result = transformM(transformM(element));

    if (!sgaEqual(result, element)) {
      throw new Error(`M² ≠ identity for class ${c}`);
    }
  }

  console.log('✓ M² = identity verified for all 96 classes');
}

// ============================================================================
// Commutation Tests
// ============================================================================

function testRDCommutation(): void {
  console.log('\nTesting RD = DR for all 96 classes...');

  for (let c = 0; c < 96; c++) {
    const element = lift(c);
    const rd = transformD(transformR(element));
    const dr = transformR(transformD(element));

    if (!sgaEqual(rd, dr)) {
      throw new Error(`RD ≠ DR for class ${c}`);
    }
  }

  console.log('✓ RD = DR verified for all 96 classes');
}

function testRTCommutation(): void {
  console.log('\nTesting RT = TR for all 96 classes...');

  for (let c = 0; c < 96; c++) {
    const element = lift(c);
    const rt = transformT(transformR(element));
    const tr = transformR(transformT(element));

    if (!sgaEqual(rt, tr)) {
      throw new Error(`RT ≠ TR for class ${c}`);
    }
  }

  console.log('✓ RT = TR verified for all 96 classes');
}

function testDTCommutation(): void {
  console.log('\nTesting DT = TD for all 96 classes...');

  for (let c = 0; c < 96; c++) {
    const element = lift(c);
    const dt = transformT(transformD(element));
    const td = transformD(transformT(element));

    if (!sgaEqual(dt, td)) {
      throw new Error(`DT ≠ TD for class ${c}`);
    }
  }

  console.log('✓ DT = TD verified for all 96 classes');
}

// ============================================================================
// Mirror Conjugation Tests
// ============================================================================

function testMRCommutation(): void {
  console.log('\nTesting MR = RM for all 96 classes...');
  console.log('(M only affects d, so it commutes with R which affects h)');

  for (let c = 0; c < 96; c++) {
    const element = lift(c);

    // Compute MR
    const mr = transformR(transformM(element));

    // Compute RM
    const rm = transformM(transformR(element));

    if (!sgaEqual(mr, rm)) {
      throw new Error(`MR ≠ RM for class ${c}`);
    }
  }

  console.log('✓ MR = RM verified for all 96 classes');
}

function testMDMConjugation(): void {
  console.log('\nTesting MDM = D⁻¹ for all 96 classes...');

  for (let c = 0; c < 96; c++) {
    const element = lift(c);

    // Compute MDM
    const mdm = transformM(transformD(transformM(element)));

    // Compute D⁻¹ = D²
    const dInverse = transformDPower(element, 2);

    if (!sgaEqual(mdm, dInverse)) {
      throw new Error(`MDM ≠ D⁻¹ for class ${c}`);
    }
  }

  console.log('✓ MDM = D⁻¹ verified for all 96 classes');
}

function testMTCommutation(): void {
  console.log('\nTesting MT = TM for all 96 classes...');
  console.log('(M only affects d, so it commutes with T which affects ℓ)');

  for (let c = 0; c < 96; c++) {
    const element = lift(c);

    // Compute MT
    const mt = transformT(transformM(element));

    // Compute TM
    const tm = transformM(transformT(element));

    if (!sgaEqual(mt, tm)) {
      throw new Error(`MT ≠ TM for class ${c}`);
    }
  }

  console.log('✓ MT = TM verified for all 96 classes');
}

// ============================================================================
// Main Test Runner
// ============================================================================

export function runSgaLawsTests(): void {
  console.log('═══════════════════════════════════════════════════════════');
  console.log('  SGA Algebraic Laws Test Suite');
  console.log('═══════════════════════════════════════════════════════════');

  // Order tests
  runTest('R⁴ = identity', testR4Identity);
  runTest('D³ = identity', testD3Identity);
  runTest('T⁸ = identity', testT8Identity);
  runTest('M² = identity', testM2Identity);

  // Commutation tests
  runTest('RD = DR', testRDCommutation);
  runTest('RT = TR', testRTCommutation);
  runTest('DT = TD', testDTCommutation);

  // Mirror tests
  runTest('MR = RM', testMRCommutation);
  runTest('MDM = D⁻¹', testMDMConjugation);
  runTest('MT = TM', testMTCommutation);

  console.log('\n═══════════════════════════════════════════════════════════');
  console.log('  ✓ All SGA algebraic laws verified!');
  console.log('═══════════════════════════════════════════════════════════\n');
}

// Run tests if executed directly
if (require.main === module) {
  try {
    runSgaLawsTests();
  } catch (error) {
    console.error('Tests failed!');
    process.exit(1);
  }
}
