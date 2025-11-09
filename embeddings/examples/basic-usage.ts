/**
 * Atlas Examples
 * Practical usage patterns and demonstrations
 */

import Atlas from '@uor-foundation/sigmatics';

console.log('='.repeat(70));
console.log('Atlas Sigil Algebra - Examples');
console.log('='.repeat(70));
console.log();

// ============================================================================
// Example 1: Basic Operations
// ============================================================================

console.log('Example 1: Basic Operations');
console.log('-'.repeat(70));

const basic1 = Atlas.prettyPrint('mark@c00');
console.log(basic1);
console.log();

const basic2 = Atlas.prettyPrint('copy@c05 . evaluate@c21');
console.log(basic2);
console.log();

const basic3 = Atlas.prettyPrint('mark@c01 || mark@c02 || mark@c03');
console.log(basic3);
console.log();

// ============================================================================
// Example 2: Transform Operations
// ============================================================================

console.log('Example 2: Transform Operations');
console.log('-'.repeat(70));

// Rotation (change quadrant)
console.log('Rotation R+1 shifts quadrant:');
const orig = Atlas.evaluateBytes('mark@c00');
const rotated = Atlas.evaluateBytes('R+1@mark@c00');
console.log(`  Original: c00 → 0x${orig.bytes[0].toString(16).toUpperCase()}`);
console.log(`  R+1:      c00 → 0x${rotated.bytes[0].toString(16).toUpperCase()}`);
console.log();

// Twist (change context ring position)
console.log('Twist T+4 rotates on 8-ring:');
const twisted = Atlas.evaluateBytes('T+4@mark@c00');
console.log(`  T+4: c00 → 0x${twisted.bytes[0].toString(16).toUpperCase()}`);
console.log();

// Mirror (flip modality)
console.log('Mirror ~ flips modality (produce ↔ consume):');
const c13 = Atlas.classInfo(Atlas.canonicalByte(13));
console.log(`  Original c13: modality=${c13.components.d}`);
const mirrored = Atlas.evaluateBytes('~@mark@c13');
const mirroredInfo = Atlas.classInfo(mirrored.bytes[0]);
console.log(`  Mirrored:     modality=${mirroredInfo.components.d}`);
console.log();

// ============================================================================
// Example 3: Class System Exploration
// ============================================================================

console.log('Example 3: Class System Exploration');
console.log('-'.repeat(70));

// Show class structure for a specific class
const classIdx = 21;
const members = Atlas.equivalenceClass(classIdx);
console.log(`Class ${classIdx} has ${members.length} member bytes:`);
console.log(
  `  ${members.map((b) => '0x' + b.toString(16).toUpperCase().padStart(2, '0')).join(', ')}`,
);
console.log();

// Show canonical representatives for first 10 classes
console.log('First 10 classes and their canonical bytes:');
for (let i = 0; i < 10; i++) {
  const byte = Atlas.canonicalByte(i);
  console.log(`  c${i.toString().padStart(2, '0')}: ${Atlas.formatClass(byte)}`);
}
console.log();

// ============================================================================
// Example 4: Belt Addressing
// ============================================================================

console.log('Example 4: Belt Addressing');
console.log('-'.repeat(70));

console.log('The Belt has 12,288 addresses across 48 pages (256 bytes each):');
console.log();

// Example addresses
const examples = [
  { page: 0, byte: 0x00 },
  { page: 17, byte: 0x2e },
  { page: 47, byte: 0xff },
];

console.log('Sample addresses:');
for (const { page, byte } of examples) {
  const addr = Atlas.beltAddress(page, byte);
  console.log(
    `  Page ${page.toString().padStart(2)}, Byte 0x${byte.toString(16).toUpperCase().padStart(2, '0')} → Address ${addr.address}`,
  );
}
console.log();

// Evaluate with page indices
console.log('Evaluating with page indices:');
const withPage = Atlas.evaluateBytes('mark@c42^+3~@17');
console.log(`  mark@c42^+3~@17`);
console.log(`    Byte: 0x${withPage.bytes[0].toString(16).toUpperCase()}`);
console.log(`    Address: ${withPage.addresses![0]}`);
console.log();

// ============================================================================
// Example 5: Operational Backend (Word Lowering)
// ============================================================================

console.log('Example 5: Operational Backend (Word Lowering)');
console.log('-'.repeat(70));

console.log('Generator words with parameters:');
const ops = [
  'mark@c00',
  'copy@c05',
  'swap@c10',
  'merge@c13',
  'split@c20',
  'quote@c30',
  'evaluate@c40',
];

for (const op of ops) {
  const result = Atlas.evaluateWords(op);
  console.log(`  ${op}`);
  console.log(`    → ${result.words.join(', ')}`);
}
console.log();

// ============================================================================
// Example 6: Complex Expressions
// ============================================================================

console.log('Example 6: Complex Expressions');
console.log('-'.repeat(70));

const complex = [
  'R+2 T+3 ~@ (copy@c05 . evaluate@c21 || swap@c42)',
  '(mark@c00 . copy@c01) || (swap@c02 . merge@c03)',
  'T+1@ (T+1@ (T+1@ mark@c00))', // triple twist
];

for (const expr of complex) {
  console.log(`Expression: ${expr}`);
  const result = Atlas.evaluate(expr);
  console.log(
    `  Bytes: ${result.literal.bytes.map((b) => '0x' + b.toString(16).toUpperCase().padStart(2, '0')).join(' ')}`,
  );
  console.log(`  Words: ${result.operational.words.length} operations`);
  console.log();
}

// ============================================================================
// Example 7: Equivalence Testing
// ============================================================================

console.log('Example 7: Equivalence Testing (≡₉₆)');
console.log('-'.repeat(70));

// Show some equivalent pairs
const testPairs = [
  [0x00, 0x01],
  [0x02, 0x03],
  [0x04, 0x05],
  [0x2a, 0x2b],
];

console.log('Testing byte equivalence:');
for (const [b1, b2] of testPairs) {
  const equiv = Atlas.equivalent(b1, b2);
  const c1 = Atlas.classIndex(b1);
  const c2 = Atlas.classIndex(b2);
  console.log(
    `  0x${b1.toString(16).toUpperCase().padStart(2, '0')} ≡₉₆ 0x${b2.toString(16).toUpperCase().padStart(2, '0')}? ${equiv} (classes: ${c1}, ${c2})`,
  );
}
console.log();

// ============================================================================
// Example 8: Class Distribution
// ============================================================================

console.log('Example 8: Class Distribution Analysis');
console.log('-'.repeat(70));

// Count how many bytes map to each class
const distribution = new Map<number, number>();
for (let byte = 0; byte < 256; byte++) {
  const classIdx = Atlas.classIndex(byte);
  distribution.set(classIdx, (distribution.get(classIdx) || 0) + 1);
}

console.log('Class size distribution:');
const sizes = Array.from(distribution.values());
const uniqueSizes = Array.from(new Set(sizes)).sort((a, b) => a - b);
for (const size of uniqueSizes) {
  const count = sizes.filter((s) => s === size).length;
  console.log(`  ${count} classes have ${size} members`);
}
console.log();

console.log(`Total: ${distribution.size} classes covering 256 bytes`);
console.log();

// ============================================================================
// Example 9: Systematic Class Enumeration
// ============================================================================

console.log('Example 9: Systematic Class Enumeration');
console.log('-'.repeat(70));

console.log('Classes by quadrant (h₂):');
for (let h2 = 0; h2 < 4; h2++) {
  const classes = Array.from({ length: 24 }, (_, i) => h2 * 24 + i);
  const bytes = classes.map((c) => Atlas.canonicalByte(c));
  console.log(`  Quadrant ${h2}: classes ${h2 * 24}..${h2 * 24 + 23}`);
  console.log(
    `    Sample bytes: ${bytes
      .slice(0, 6)
      .map((b) => '0x' + b.toString(16).toUpperCase().padStart(2, '0'))
      .join(' ')} ...`,
  );
}
console.log();

// ============================================================================
// Example 10: Practical Use Case - Building Expressions
// ============================================================================

console.log('Example 10: Building Expressions Programmatically');
console.log('-'.repeat(70));

// Function to build a sequence of operations
function buildSequence(ops: string[]): string {
  return ops.join(' . ');
}

// Function to build parallel operations
function buildParallel(ops: string[]): string {
  return ops.join(' || ');
}

const seq = buildSequence(['mark@c00', 'copy@c01', 'swap@c02']);
console.log(`Sequence: ${seq}`);
console.log(Atlas.prettyPrint(seq));

const par = buildParallel(['mark@c00', 'mark@c01', 'mark@c02']);
console.log(`Parallel: ${par}`);
console.log(Atlas.prettyPrint(par));

console.log('='.repeat(70));
console.log('End of Examples');
console.log('='.repeat(70));
