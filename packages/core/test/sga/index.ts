/**
 * SGA Test Suite Runner
 *
 * Runs all SGA tests including:
 * - Group algebra inversions (ℝ[ℤ₄] and ℝ[ℤ₃])
 * - Algebraic laws (R⁴=id, D³=id, T⁸=id, M²=id, commutation, conjugation)
 * - Bridge commutative diagrams (1344 tests)
 */

import { runGroupAlgebraTests } from './group-algebras.test';
import { runSgaLawsTests } from './laws.test';
import { runBridgeTests } from './bridge.test';
import { runBugFixTests } from './bug-fixes.test';

export function runAllSgaTests(): void {
  console.log('\n\n');
  console.log('╔═══════════════════════════════════════════════════════════╗');
  console.log('║                                                           ║');
  console.log('║        SIGMATICS v0.3.0 - SGA TEST SUITE                 ║');
  console.log('║                                                           ║');
  console.log('╚═══════════════════════════════════════════════════════════╝');
  console.log('\n');

  try {
    // Run group algebra inversion tests
    runGroupAlgebraTests();

    // Run algebraic laws tests
    runSgaLawsTests();

    // Run bridge commutative diagram tests
    runBridgeTests();

    // Run bug fix verification tests (v0.3.1)
    runBugFixTests();

    console.log('\n\n');
    console.log('╔═══════════════════════════════════════════════════════════╗');
    console.log('║                                                           ║');
    console.log('║        ✓ ALL SGA TESTS PASSED!                           ║');
    console.log('║                                                           ║');
    console.log('║  v0.3.0 Implementation Verified:                         ║');
    console.log('║  • All algebraic laws hold                               ║');
    console.log('║  • All commutative diagrams verified                     ║');
    console.log('║  • SGA correctly implements class transforms             ║');
    console.log('║                                                           ║');
    console.log('╚═══════════════════════════════════════════════════════════╝');
    console.log('\n');
  } catch (error) {
    console.error('\n\n');
    console.error('╔═══════════════════════════════════════════════════════════╗');
    console.error('║                                                           ║');
    console.error('║        ✗ SGA TESTS FAILED                                ║');
    console.error('║                                                           ║');
    console.error('╚═══════════════════════════════════════════════════════════╝');
    console.error('\n');
    throw error;
  }
}

// Run if executed directly
if (require.main === module) {
  try {
    runAllSgaTests();
  } catch (error) {
    process.exit(1);
  }
}
