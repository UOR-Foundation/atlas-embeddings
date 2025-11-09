/**
 * Quick Validation Script
 * Tests core functionality without running full test suite
 */

// FIX: Declare process for Node.js environment compatibility
declare const process: any;

import Atlas from '@uor-foundation/sigmatics';

console.log('Quick Validation Tests');
console.log('='.repeat(50));
console.log();

let passed = 0;
let failed = 0;

function test(name: string, fn: () => boolean): void {
  try {
    const result = fn();
    if (result) {
      console.log(`✓ ${name}`);
      passed++;
    } else {
      console.log(`✗ ${name} - assertion failed`);
      failed++;
    }
  } catch (error: any) {
    console.log(`✗ ${name} - ${error.message}`);
    failed++;
  }
}

// Test 1: Basic evaluation
test('Evaluate mark@c21 → 0x2A', () => {
  const result = Atlas.evaluateBytes('mark@c21');
  return result.bytes[0] === 0x2a;
});

// Test 2: Sequential composition
test('Sequential composition', () => {
  const result = Atlas.evaluateBytes('evaluate@c21 . copy@c05');
  return result.bytes.length === 2 && result.bytes[0] === 0x2a && result.bytes[1] === 0x0a;
});

// Test 3: Class system
test('Class index 0x2A → 21', () => {
  return Atlas.classIndex(0x2a) === 21;
});

// Test 4: Canonical byte
test('Canonical byte class 21 → 0x2A', () => {
  return Atlas.canonicalByte(21) === 0x2a;
});

// Test 5: Equivalence
test('0x00 ≡₉₆ 0x01', () => {
  return Atlas.equivalent(0x00, 0x01);
});

// Test 6: Transform R+1
test('R+1@ mark@c00 transforms correctly', () => {
  const result = Atlas.evaluateBytes('R+1@mark@c00');
  const classIdx = Atlas.classIndex(result.bytes[0]);
  // c00 is class 0 (h2=0,d=0,l=0), R+1 gives (h2=1,d=0,l=0) = class 24
  return classIdx === 24;
});

// Test 7: Transform T+4
test('T+4@ mark@c00 transforms correctly', () => {
  const result = Atlas.evaluateBytes('T+4@mark@c00');
  // c00 is class 0 (h2=0,d=0,l=0), T+4 gives (h2=0,d=0,l=4) = class 4
  return Atlas.classIndex(result.bytes[0]) === 4;
});

// Test 8: Belt address
test('Belt address computation', () => {
  const addr = Atlas.beltAddress(17, 0x2e);
  return addr.address === 4398;
});

// Test 9: Parse and evaluate
test('Parse → evaluate pipeline', () => {
  const ast = Atlas.parse('mark@c42');
  return ast !== null && ast.kind === 'Par';
});

// Test 10: Pretty print
test('Pretty print produces output', () => {
  const output = Atlas.prettyPrint('mark@c00');
  return output.includes('0x00');
});

console.log();
console.log('='.repeat(50));
console.log(`Results: ${passed} passed, ${failed} failed`);

if (failed === 0) {
  console.log('✓ All validation tests passed!');
  process.exit(0);
} else {
  console.log('✗ Some tests failed');
  process.exit(1);
}
