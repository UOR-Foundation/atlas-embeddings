/**
 * Documentation Validation Script
 * Tests all code examples from the documentation
 */

import Atlas from '@uor-foundation/sigmatics';

console.log('='.repeat(70));
console.log('Documentation Code Example Validation');
console.log('='.repeat(70));
console.log();

let passed = 0;
let failed = 0;

function test(name: string, fn: () => void) {
  try {
    fn();
    console.log(`✓ ${name}`);
    passed++;
  } catch (error) {
    console.log(`✗ ${name}`);
    console.log(`  Error: ${error}`);
    failed++;
  }
}

// ============================================================================
// From README.md
// ============================================================================

console.log('Testing README.md examples...\n');

test('Basic evaluate', () => {
  const result = Atlas.evaluate('evaluate@c21 . copy@c05');
  if (!result.literal.bytes || !result.operational.words) {
    throw new Error('Missing expected properties');
  }
});

test('Pretty print', () => {
  const output = Atlas.prettyPrint('mark@c42^+3~@17');
  if (!output.includes('Expression:')) {
    throw new Error('Output missing expected format');
  }
});

test('Parse', () => {
  const ast = Atlas.parse('copy@c05 . swap@c10');
  if (!ast) throw new Error('Parse returned falsy value');
});

test('Evaluate bytes', () => {
  const result = Atlas.evaluateBytes('mark@c21');
  if (!result.bytes || !Array.isArray(result.bytes)) {
    throw new Error('Invalid bytes result');
  }
});

test('Evaluate words', () => {
  const result = Atlas.evaluateWords('evaluate@c21');
  if (!result.words || !Array.isArray(result.words)) {
    throw new Error('Invalid words result');
  }
});

test('Class index', () => {
  const classIdx = Atlas.classIndex(0x2a);
  if (classIdx !== 21) {
    throw new Error(`Expected class 21, got ${classIdx}`);
  }
});

test('Canonical byte', () => {
  const byte = Atlas.canonicalByte(21);
  if (byte !== 0x2a) {
    throw new Error(`Expected 0x2A, got ${byte}`);
  }
});

test('Equivalent', () => {
  const equiv = Atlas.equivalent(0x00, 0x01);
  if (!equiv) {
    throw new Error('Expected bytes to be equivalent');
  }
});

test('Equivalence class', () => {
  const members = Atlas.equivalenceClass(0);
  if (!Array.isArray(members) || members.length === 0) {
    throw new Error('Invalid equivalence class result');
  }
});

test('Class info structure', () => {
  const info = Atlas.classInfo(0x2a);
  if (info.classIndex !== 21) {
    throw new Error(`Wrong classIndex: ${info.classIndex}`);
  }
  // SigilComponents: h2 (0-3), d (0-2), l (0-7)
  if (
    !info.components ||
    typeof info.components.h2 !== 'number' ||
    info.components.h2 < 0 ||
    info.components.h2 > 3
  ) {
    throw new Error('Missing or invalid components.h2 (must be 0-3)');
  }
  if (typeof info.components.d !== 'number' || info.components.d < 0 || info.components.d > 2) {
    throw new Error('Missing or invalid components.d (must be 0-2)');
  }
  if (typeof info.components.l !== 'number' || info.components.l < 0 || info.components.l > 7) {
    throw new Error('Missing or invalid components.l (must be 0-7)');
  }
  if (info.canonicalByte !== 0x2a) {
    throw new Error(`Wrong canonicalByte: ${info.canonicalByte}`);
  }
});

test('Belt address', () => {
  const addr = Atlas.beltAddress(17, 0x2e);
  if (addr.page !== 17) {
    throw new Error(`Wrong page: ${addr.page}`);
  }
  if (addr.byte !== 46) {
    throw new Error(`Wrong byte: ${addr.byte}`);
  }
  if (addr.address !== 4398) {
    throw new Error(`Wrong address: ${addr.address}`);
  }
});

test('Decode belt address', () => {
  const decomp = Atlas.decodeBeltAddress(4398);
  if (decomp.page !== 17 || decomp.byte !== 46 || decomp.address !== 4398) {
    throw new Error('Decoded address mismatch');
  }
});

test('All classes', () => {
  const classes = Atlas.allClasses();
  // Atlas has exactly 96 equivalence classes (4 quadrants × 3 modalities × 8 context slots)
  const TOTAL_CLASSES = 96;
  if (classes.length !== TOTAL_CLASSES) {
    throw new Error(`Expected ${TOTAL_CLASSES} classes, got ${classes.length}`);
  }
  if (typeof classes[0].index !== 'number' || typeof classes[0].byte !== 'number') {
    throw new Error('Invalid class structure');
  }
});

test('Byte class mapping', () => {
  const mapping = Atlas.byteClassMapping();
  // Map all 256 possible byte values (0x00 to 0xFF) to their classes
  const TOTAL_BYTES = 256;
  if (mapping.length !== TOTAL_BYTES) {
    throw new Error(`Expected ${TOTAL_BYTES} mappings, got ${mapping.length}`);
  }
});

// ============================================================================
// From packages/core/README.md
// ============================================================================

console.log('\nTesting packages/core/README.md examples...\n');

test('Core: Parse', () => {
  const ast = Atlas.parse('copy@c05 . swap@c10');
  if (!ast) throw new Error('Parse failed');
});

test('Core: Evaluate bytes', () => {
  const bytes = Atlas.evaluateBytes('mark@c21');
  if (!bytes.bytes) throw new Error('Missing bytes');
});

test('Core: Evaluate words', () => {
  const words = Atlas.evaluateWords('evaluate@c21');
  if (!words.words) throw new Error('Missing words');
});

test('Core: Complete evaluation', () => {
  const result = Atlas.evaluate('copy@c05');
  if (!result.ast || !result.literal || !result.operational) {
    throw new Error('Missing result properties');
  }
});

test('Core: Class info', () => {
  const info = Atlas.classInfo(0x2a);
  if (info.classIndex !== 21) {
    throw new Error('Wrong class index');
  }
});

test('Core: Equivalent', () => {
  const result = Atlas.equivalent(0x2a, 0x2b);
  if (!result) throw new Error('Should be equivalent');
});

test('Core: Equivalence class', () => {
  const members = Atlas.equivalenceClass(21);
  if (!Array.isArray(members)) throw new Error('Not an array');
});

test('Core: Belt address with correct byte value', () => {
  const addr = Atlas.beltAddress(17, 0x2a);
  if (addr.byte !== 42) {
    throw new Error(`Expected byte=42, got ${addr.byte}`);
  }
  if (addr.address !== 4394) {
    throw new Error(`Expected address=4394, got ${addr.address}`);
  }
});

test('Core: Decode belt address', () => {
  const result = Atlas.decodeBeltAddress(4394);
  if (result.byte !== 42) {
    throw new Error(`Expected byte=42, got ${result.byte}`);
  }
});

// ============================================================================
// From QUICKSTART.md
// ============================================================================

console.log('\nTesting QUICKSTART.md examples...\n');

test('Quick: Evaluate bytes', () => {
  const result = Atlas.evaluateBytes('mark@c21');
  if (!result.bytes || result.bytes.length === 0) {
    throw new Error('No bytes returned');
  }
});

test('Quick: Full evaluate', () => {
  const full = Atlas.evaluate('copy@c05');
  if (!full.literal.bytes || !full.operational.words) {
    throw new Error('Missing expected properties');
  }
});

test('Quick: Class index', () => {
  const classIdx = Atlas.classIndex(0x2a);
  if (classIdx !== 21) throw new Error('Wrong class index');
});

test('Quick: Canonical byte', () => {
  const byte = Atlas.canonicalByte(21);
  if (byte !== 0x2a) throw new Error('Wrong canonical byte');
});

test('Quick: Equivalent', () => {
  const result = Atlas.equivalent(0x00, 0x01);
  if (!result) throw new Error('Should be equivalent');
});

test('Quick: Transforms', () => {
  Atlas.evaluateBytes('R+1@ mark@c00');
  Atlas.evaluateBytes('T+4@ mark@c00');
  Atlas.evaluateBytes('~@ mark@c13');
  Atlas.evaluateBytes('R+2 T+3 ~@ mark@c07');
});

test('Quick: Belt address', () => {
  const addr = Atlas.beltAddress(17, 0x2e);
  if (addr.address !== 4398) {
    throw new Error(`Expected 4398, got ${addr.address}`);
  }
});

test('Quick: Class info structure', () => {
  const info = Atlas.classInfo(0x2a);
  if (info.classIndex !== 21) throw new Error('Wrong classIndex');
  if (info.components.h2 !== 0) throw new Error('Wrong h2');
  if (info.components.d !== 2) throw new Error('Wrong d');
  if (info.components.l !== 5) throw new Error('Wrong l');
  if (info.canonicalByte !== 0x2a) throw new Error('Wrong canonicalByte');
});

test('Quick: Equivalence class', () => {
  const members = Atlas.equivalenceClass(21);
  if (!Array.isArray(members) || members.length === 0) {
    throw new Error('Invalid equivalence class');
  }
});

test('Quick: Pretty print', () => {
  const output = Atlas.prettyPrint('mark@c42^+3~@17');
  if (!output || typeof output !== 'string') {
    throw new Error('Invalid pretty print output');
  }
});

// ============================================================================
// Complex examples from README
// ============================================================================

console.log('\nTesting complex examples...\n');

test('Sequential composition', () => {
  const result = Atlas.evaluateBytes('evaluate@c21 . copy@c05');
  if (result.bytes.length !== 2) {
    throw new Error(`Expected 2 bytes, got ${result.bytes.length}`);
  }
});

test('Parallel composition', () => {
  const result = Atlas.evaluateBytes('mark@c01 || mark@c02');
  if (result.bytes.length !== 2) {
    throw new Error('Expected 2 bytes from parallel');
  }
});

test('Prefix transform', () => {
  Atlas.evaluateBytes('R+1@ (copy@c05 . evaluate@c21)');
});

test('Postfix transform', () => {
  Atlas.evaluateBytes('mark@c42^+3~');
});

test('Combined transforms', () => {
  Atlas.evaluateBytes('R+2 T+3 ~@ mark@c07');
});

test('Belt addressing', () => {
  const result = Atlas.evaluateBytes('mark@c42^+3~@17');
  if (!result.addresses || result.addresses.length === 0) {
    throw new Error('Missing belt addresses');
  }
});

test('Format bytes', () => {
  const formatted = Atlas.formatBytes([0x2a, 0x0a]);
  if (!formatted || typeof formatted !== 'string') {
    throw new Error('Invalid format output');
  }
});

test('Format class', () => {
  const formatted = Atlas.formatClass(0x2a);
  if (!formatted || typeof formatted !== 'string') {
    throw new Error('Invalid format output');
  }
});

// ============================================================================
// Summary
// ============================================================================

console.log('\n' + '='.repeat(70));
console.log(`Results: ${passed} passed, ${failed} failed`);
console.log('='.repeat(70));

if (failed > 0) {
  process.exit(1);
}
