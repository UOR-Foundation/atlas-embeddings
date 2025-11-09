/**
 * Bridge Commutative Diagram Tests
 *
 * This file tests the fundamental correctness property of v0.3.0:
 *
 *   For all transforms g ∈ {R, D, T, M} and classes c ∈ [0,95]:
 *   project(g_alg(lift(c))) === g_perm(c)
 *
 * This is THE critical test that proves the SGA implementation correctly
 * implements the class transform semantics.
 */

import { validateAll, summarizeResults } from '../../src/bridge/validation';

// ============================================================================
// Main Test Runner
// ============================================================================

export function runBridgeTests(): void {
  console.log('═══════════════════════════════════════════════════════════');
  console.log('  Bridge Commutative Diagram Test Suite');
  console.log('═══════════════════════════════════════════════════════════');

  console.log('\nRunning comprehensive validation...');
  console.log('This validates all commutative diagrams for:');
  console.log('  - Lift/project round trip (96 tests)');
  console.log('  - R transform (288 tests: 96 classes × 3 powers)');
  console.log('  - D transform (192 tests: 96 classes × 2 powers)');
  console.log('  - T transform (672 tests: 96 classes × 7 powers)');
  console.log('  - M transform (96 tests)');
  console.log('  Total: 1344 tests\n');

  const result = validateAll();

  console.log(summarizeResults(result.results));

  if (!result.allPassed) {
    console.error('\n✗ Bridge validation FAILED!');
    console.error('The SGA implementation does not correctly match the permutation system.');
    throw new Error('Bridge validation failed');
  }

  console.log('\n═══════════════════════════════════════════════════════════');
  console.log('  ✓ All commutative diagrams verified!');
  console.log('  ✓ SGA transforms correctly implement class permutations!');
  console.log('═══════════════════════════════════════════════════════════\n');
}

// Run tests if executed directly
if (require.main === module) {
  try {
    runBridgeTests();
  } catch (error) {
    console.error('Tests failed!');
    process.exit(1);
  }
}
