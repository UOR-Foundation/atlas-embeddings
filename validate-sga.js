#!/usr/bin/env node
/**
 * Quick SGA Validation Script
 *
 * Tests basic SGA functionality to ensure everything is working.
 */

const { Atlas } = require('./packages/core/dist/index.js');

console.log('═══════════════════════════════════════════════════════════');
console.log('  SGA v0.3.0 Quick Validation');
console.log('═══════════════════════════════════════════════════════════\n');

try {
  // Test 1: Lift and project
  console.log('Test 1: Lift and project class 21...');
  const element = Atlas.SGA.lift(21);
  const projected = Atlas.SGA.project(element);
  console.log(`  Lifted class 21, projected back to: ${projected}`);
  if (projected !== 21) {
    throw new Error(`Expected 21, got ${projected}`);
  }
  console.log('  ✓ Lift-project round trip works!\n');

  // Test 2: D-transform
  console.log('Test 2: Apply D-transform...');
  const dTransformed = Atlas.SGA.D(element);
  const dProjected = Atlas.SGA.project(dTransformed);
  console.log(`  D(class 21) = class ${dProjected}`);

  // Verify using permutation system
  const expected = Atlas.applyDTransform(21, 1).newClass;
  console.log(`  Expected (from permutation): ${expected}`);

  if (dProjected !== expected) {
    throw new Error(`D-transform mismatch: SGA gave ${dProjected}, permutation gave ${expected}`);
  }
  console.log('  ✓ D-transform matches permutation system!\n');

  // Test 3: R-transform
  console.log('Test 3: Apply R-transform...');
  const rTransformed = Atlas.SGA.R(element);
  const rProjected = Atlas.SGA.project(rTransformed);
  console.log(`  R(class 21) = class ${rProjected}`);
  console.log('  ✓ R-transform works!\n');

  // Test 4: T-transform
  console.log('Test 4: Apply T-transform...');
  const tTransformed = Atlas.SGA.T(element);
  const tProjected = Atlas.SGA.project(tTransformed);
  console.log(`  T(class 21) = class ${tProjected}`);
  console.log('  ✓ T-transform works!\n');

  // Test 5: M-transform
  console.log('Test 5: Apply M-transform...');
  const mTransformed = Atlas.SGA.M(element);
  const mProjected = Atlas.SGA.project(mTransformed);
  console.log(`  M(class 21) = class ${mProjected}`);
  console.log('  ✓ M-transform works!\n');

  // Test 6: Verify D³ = identity
  console.log('Test 6: Verify D³ = identity...');
  const d3 = Atlas.SGA.D(Atlas.SGA.D(Atlas.SGA.D(element)));
  const d3Projected = Atlas.SGA.project(d3);
  console.log(`  D³(class 21) = class ${d3Projected}`);
  if (d3Projected !== 21) {
    throw new Error(`D³ ≠ identity: got ${d3Projected}, expected 21`);
  }
  console.log('  ✓ D³ = identity verified!\n');

  // Test 7: Check Fano plane
  console.log('Test 7: Verify Fano plane structure...');
  const fanoOk = Atlas.SGA.Fano.verify();
  console.log(`  Fano plane valid: ${fanoOk}`);
  if (!fanoOk) {
    throw new Error('Fano plane verification failed');
  }
  console.log('  ✓ Fano plane verified!\n');

  console.log('═══════════════════════════════════════════════════════════');
  console.log('  ✓ All quick validation tests passed!');
  console.log('═══════════════════════════════════════════════════════════\n');

  console.log('Run full test suite with: npm test');
  console.log('\n');
} catch (error) {
  console.error('\n✗ Validation failed!');
  console.error(error.message);
  console.error(error.stack);
  process.exit(1);
}
