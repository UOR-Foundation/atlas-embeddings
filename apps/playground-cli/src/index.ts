#!/usr/bin/env ts-node
/**
 * Atlas Interactive Playground
 * Run sigil expressions and explore results
 */

import Atlas from '@uor-foundation/sigmatics';

// Color helpers for terminal output
const colors = {
  reset: '\x1b[0m',
  bright: '\x1b[1m',
  cyan: '\x1b[36m',
  green: '\x1b[32m',
  yellow: '\x1b[33m',
  blue: '\x1b[34m',
  magenta: '\x1b[35m',
};

function header(text: string) {
  console.log(`\n${colors.bright}${colors.cyan}${'='.repeat(70)}${colors.reset}`);
  console.log(`${colors.bright}${colors.cyan}${text}${colors.reset}`);
  console.log(`${colors.cyan}${'='.repeat(70)}${colors.reset}\n`);
}

function subheader(text: string) {
  console.log(`${colors.bright}${colors.blue}${text}${colors.reset}`);
  console.log(`${colors.blue}${'-'.repeat(70)}${colors.reset}`);
}

function success(text: string) {
  console.log(`${colors.green}✓${colors.reset} ${text}`);
}

function info(text: string) {
  console.log(`${colors.yellow}→${colors.reset} ${text}`);
}

// ============================================================================
// Playground Demos
// ============================================================================

header('🌐 Atlas Sigil Algebra - Interactive Playground');

// Demo 1: Basic Expression
subheader('Demo 1: Evaluating a Simple Expression');
const expr1 = 'mark@c21';
info(`Expression: "${expr1}"`);
const result1 = Atlas.evaluate(expr1);
console.log(`Byte output: 0x${result1.literal.bytes[0].toString(16).toUpperCase()}`);
console.log(`Class: ${Atlas.classIndex(result1.literal.bytes[0])}`);
console.log(`Words: ${result1.operational.words.join(', ')}`);
success('Evaluation complete!\n');

// Demo 2: Sequential Composition
subheader('Demo 2: Sequential Composition');
const expr2 = 'evaluate@c21 . copy@c05';
info(`Expression: "${expr2}"`);
info('Note: Sequential composition executes right-to-left');
const result2 = Atlas.evaluate(expr2);
console.log(
  `Bytes: ${result2.literal.bytes.map((b) => '0x' + b.toString(16).toUpperCase()).join(' ')}`,
);
success('Multiple operations composed!\n');

// Demo 3: Parallel Composition
subheader('Demo 3: Parallel Composition');
const expr3 = 'mark@c01 || mark@c02 || mark@c03';
info(`Expression: "${expr3}"`);
const result3 = Atlas.evaluate(expr3);
console.log(
  `Bytes: ${result3.literal.bytes.map((b) => '0x' + b.toString(16).toUpperCase()).join(' ')}`,
);
success('Parallel branches evaluated!\n');

// Demo 4: Transform Operations
subheader('Demo 4: Transform Operations');
const transforms = [
  { expr: 'mark@c00', desc: 'Original' },
  { expr: 'R+1@mark@c00', desc: 'Rotated +1 quadrant' },
  { expr: 'T+4@mark@c00', desc: 'Twisted +4 on ring' },
  { expr: '~@mark@c13', desc: 'Mirrored modality' },
];

for (const { expr, desc } of transforms) {
  const result = Atlas.evaluateBytes(expr);
  const byte = result.bytes[0];
  const classIdx = Atlas.classIndex(byte);
  console.log(
    `${desc.padEnd(25)} → 0x${byte.toString(16).toUpperCase().padStart(2, '0')} (class ${classIdx})`,
  );
}
success('Transforms applied!\n');

// Demo 5: Class Equivalence
subheader('Demo 5: Class Equivalence Testing');
info('Testing which bytes belong to the same class...');
const testBytes = [0x00, 0x01, 0x02, 0x30, 0x31];
const classes = testBytes.map((b) => ({
  byte: b,
  class: Atlas.classIndex(b),
}));

console.log('\nByte → Class mapping:');
for (const { byte, class: c } of classes) {
  console.log(`  0x${byte.toString(16).toUpperCase().padStart(2, '0')} → class ${c}`);
}

console.log('\nEquivalence tests:');
console.log(`  0x00 ≡₉₆ 0x01? ${Atlas.equivalent(0x00, 0x01)}`);
console.log(`  0x00 ≡₉₆ 0x02? ${Atlas.equivalent(0x00, 0x02)}`);
console.log(`  0x00 ≡₉₆ 0x30? ${Atlas.equivalent(0x00, 0x30)}`);
success('Equivalence tested!\n');

// Demo 6: Belt Addressing
subheader('Demo 6: Belt Addressing System');
info('The Belt has 12,288 addresses across 48 pages');
const beltExamples = [
  { page: 0, byte: 0x00 },
  { page: 17, byte: 0x2e },
  { page: 47, byte: 0xff },
];

console.log('\nSample addresses:');
for (const { page, byte } of beltExamples) {
  const addr = Atlas.beltAddress(page, byte);
  console.log(
    `  Page ${page.toString().padStart(2)}, Byte 0x${byte.toString(16).toUpperCase().padStart(2, '0')} → Address ${addr.address.toString().padStart(5)}`,
  );
}

info('\nEvaluating with belt address:');
const exprWithPage = 'mark@c42^+3~@17';
const resultWithPage = Atlas.evaluateBytes(exprWithPage);
console.log(`  Expression: "${exprWithPage}"`);
console.log(`  Byte: 0x${resultWithPage.bytes[0].toString(16).toUpperCase()}`);
console.log(`  Belt Address: ${resultWithPage.addresses![0]}`);
success('Belt addressing demonstrated!\n');

// Demo 7: Exploring a Class
subheader('Demo 7: Exploring Class Structure');
const exploreClass = 21;
info(`Examining class ${exploreClass}...`);

const canonical = Atlas.canonicalByte(exploreClass);
const classInfo = Atlas.classInfo(canonical);
const members = Atlas.equivalenceClass(exploreClass);

console.log(`\nCanonical byte: 0x${canonical.toString(16).toUpperCase()}`);
console.log(
  `Components: h₂=${classInfo.components.h2}, d=${classInfo.components.d}, ℓ=${classInfo.components.l}`,
);
console.log(`Class has ${members.length} member bytes`);
console.log(
  `Members: ${members
    .slice(0, 8)
    .map((b) => '0x' + b.toString(16).toUpperCase())
    .join(', ')}...`,
);
success('Class explored!\n');

// Demo 8: Complex Expression
subheader('Demo 8: Complex Nested Expression');
const complexExpr = 'R+2 T+3 ~@ (copy@c05 . evaluate@c21 || swap@c42)';
info(`Expression: "${complexExpr}"`);
info('This combines: transforms, sequential, and parallel composition');

const complexResult = Atlas.evaluate(complexExpr);
console.log(
  `\nBytes: ${complexResult.literal.bytes.map((b) => '0x' + b.toString(16).toUpperCase()).join(' ')}`,
);
console.log(`Words: ${complexResult.operational.words.length} operations generated`);
console.log(`\nOperational trace:`);
for (const word of complexResult.operational.words.slice(0, 10)) {
  console.log(`  ${word}`);
}
if (complexResult.operational.words.length > 10) {
  console.log(`  ... (${complexResult.operational.words.length - 10} more)`);
}
success('Complex expression evaluated!\n');

// Demo 9: All Generators
subheader('Demo 9: All Seven Generators');
info('Demonstrating all seven fundamental operations:');

const generators = [
  { gen: 'mark', desc: 'Introduce/remove distinction' },
  { gen: 'copy', desc: 'Comultiplication (fan-out)' },
  { gen: 'swap', desc: 'Symmetry/braid' },
  { gen: 'merge', desc: 'Fold/meet operation' },
  { gen: 'split', desc: 'Case analysis' },
  { gen: 'quote', desc: 'Suspend computation' },
  { gen: 'evaluate', desc: 'Force/discharge' },
];

console.log();
for (const { gen, desc } of generators) {
  const expr = `${gen}@c05`;
  const result = Atlas.evaluateWords(expr);
  console.log(`  ${gen.padEnd(10)} ${desc.padEnd(30)} → ${result.words.join(', ')}`);
}
success('All generators demonstrated!\n');

// Demo 10: Statistics
subheader('Demo 10: System Statistics');
const allClasses = Atlas.allClasses();
const byteMapping = Atlas.byteClassMapping();

console.log(`Total classes: ${allClasses.length}`);
console.log(`Total byte space: ${byteMapping.length}`);

// Count class sizes
const distribution = new Map<number, number>();
for (let byte = 0; byte < 256; byte++) {
  const classIdx = Atlas.classIndex(byte);
  distribution.set(classIdx, (distribution.get(classIdx) || 0) + 1);
}

const sizes = Array.from(distribution.values());
const uniqueSizes = Array.from(new Set(sizes)).sort((a, b) => a - b);

console.log(`\nClass size distribution:`);
for (const size of uniqueSizes) {
  const count = sizes.filter((s) => s === size).length;
  console.log(`  ${count} classes with ${size} members`);
}

console.log(`\nBelt capacity: 12,288 addresses (48 pages × 256 bytes)`);
success('Statistics computed!\n');

// ============================================================================
// Interactive Prompt
// ============================================================================

header('🎯 Try Your Own Expressions!');

console.log('You can now experiment with Atlas expressions. Try these:');
console.log();
console.log(`  ${colors.yellow}Atlas.evaluate("mark@c42")${colors.reset}`);
console.log(`  ${colors.yellow}Atlas.prettyPrint("R+1@ copy@c05")${colors.reset}`);
console.log(`  ${colors.yellow}Atlas.classInfo(0x2A)${colors.reset}`);
console.log(`  ${colors.yellow}Atlas.equivalenceClass(21)${colors.reset}`);
console.log();
console.log('Or modify this file to add your own demos!');
console.log();

header('✨ Playground Complete!');
console.log('For more examples, run: npm run example');
console.log('To run tests, run: npm test');
console.log('See README.md for full documentation\n');
