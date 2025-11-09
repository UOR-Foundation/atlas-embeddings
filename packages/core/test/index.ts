/**
 * Atlas Test Suite
 * Includes all test vectors from formal specification v1.0 and
 * comprehensive unit tests for all functions.
 */

// FIX: Declare require and module for Node.js environment compatibility
declare const require: any;
declare const module: any;

import { Atlas } from '../src/api';
import { tokenize } from '../src/lexer';
import * as AtlasClass from '../src/class-system';
import { runGroupAlgebraTests } from './sga/group-algebras.test';
import { runSgaLawsTests } from './sga/laws.test';
import { runBridgeTests } from './sga/bridge.test';
import { runBugFixTests } from './sga/bug-fixes.test';

// ============================================================================
// Test Utilities
// ============================================================================

function assertEqual<T>(actual: T, expected: T, message: string): void {
  const actualStr = JSON.stringify(actual);
  const expectedStr = JSON.stringify(expected);
  if (actualStr !== expectedStr) {
    throw new Error(`${message}\n  Expected: ${expectedStr}\n  Actual: ${actualStr}`);
  }
}

function assertArrayEqual<T>(actual: T[], expected: T[], message: string): void {
  if (actual.length !== expected.length) {
    throw new Error(`${message}\n  Expected length: ${expected.length}, but got ${actual.length}`);
  }
  const sortedActual = JSON.stringify([...actual].sort());
  const sortedExpected = JSON.stringify([...expected].sort());

  if (sortedActual !== sortedExpected) {
    throw new Error(
      `${message}\n  Expected: ${JSON.stringify(expected)}\n  Actual:   ${JSON.stringify(actual)}`,
    );
  }
}

function assertThrows(fn: () => void, message: string, expectedError: string) {
  try {
    fn();
    throw new Error(`Expected function to throw, but it did not. ${message}`);
  } catch (e: any) {
    if (!e.message.includes(expectedError)) {
      throw new Error(
        `${message}\n  Expected error message to include: "${expectedError}"\n  Actual error: "${e.message}"`,
      );
    }
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
// Specification Test Vectors (Section 7)
// ============================================================================

function runSpecificationTests(): void {
  console.log('Running Specification Test Vectors...\n');

  // Test 1: Single sigil
  runTest('Test 1: Single sigil c21', () => {
    const result = Atlas.evaluateBytes('mark@c21');
    assertArrayEqual(result.bytes, [0x2a], 'Test 1: c21 → 0x2A');
  });

  // Test 2: Three ops (seq+par)
  runTest('Test 2: Three ops - evaluate@c21 . copy@c05 || swap@c72', () => {
    const result = Atlas.evaluateBytes('evaluate@c21 . copy@c05 || swap@c72');
    assertArrayEqual(
      result.bytes,
      [0x2a, 0x0a, 0xc0],
      'Test 2: Multiple ops in sequence and parallel',
    );
  });

  // Test 3: Prefixed transform
  runTest('Test 3: Prefixed transform R+1@ (copy@c05 . evaluate@c21)', () => {
    const result = Atlas.evaluateBytes('R+1@ (copy@c05 . evaluate@c21)');
    assertArrayEqual(result.bytes, [0x4a, 0x6a], 'Test 3: R+1 transform applied to sequence');
  });

  // Test 4: Postfix transforms with page
  runTest('Test 4: Postfix transforms c42^+3~@17', () => {
    const result = Atlas.evaluateBytes('mark@c42^+3~@17');
    assertEqual(result.bytes[0], 0x5a, 'Test 4: Byte value');
    assertEqual(result.addresses![0], 4442, 'Test 4: Belt address');
  });

  // Test 5: Context marching
  runTest('Test 5: Context marching T+4@ c00', () => {
    const result = Atlas.evaluateBytes('T+4@mark@c00');
    assertArrayEqual(result.bytes, [0x08], 'Test 5: T+4 applied to c00');
  });

  // Test 6: Mirror modality
  runTest('Test 6: Mirror modality ~@ c13', () => {
    const result = Atlas.evaluateBytes('~@mark@c13');
    assertArrayEqual(result.bytes, [0x2a], 'Test 6: Mirror flips modality');
  });

  // Test 7: Rotate+twist
  runTest('Test 7: Rotate+twist R+2 T+3 @ c07', () => {
    const result = Atlas.evaluateBytes('R+2 T+3@mark@c07');
    assertArrayEqual(result.bytes, [0x84], 'Test 7: Combined R+2 T+3');
  });

  // Test 8: Error - out of range
  runTest('Test 8: Error handling for c96', () => {
    assertThrows(
      () => {
        Atlas.evaluateBytes('mark@c96');
      },
      'Should have thrown error for c96',
      'out of range',
    );
  });

  console.log('\n✓ All specification tests passed!\n');
}

// ============================================================================
// Lexer Tests
// ============================================================================

function runLexerTests(): void {
  console.log('Running Lexer Unit Tests...\n');

  runTest('Lexer: tokenize single-character tokens', () => {
    const tokens = tokenize('. ( ) @ ^ ~ + -');
    const types = tokens.map((t) => t.type);
    assertArrayEqual(
      types,
      ['DOT', 'LPAREN', 'RPAREN', 'AT', 'CARET', 'TILDE', 'PLUS', 'MINUS', 'EOF'],
      'Correctly tokenizes single chars',
    );
  });

  runTest('Lexer: tokenize multi-character tokens', () => {
    const tokens = tokenize('||');
    assertEqual(tokens[0].type, 'PARALLEL', 'Correctly tokenizes ||');
  });

  runTest('Lexer: tokenize keywords and identifiers', () => {
    const tokens = tokenize('mark copy R T');
    const types = tokens.map((t) => t.type);
    assertArrayEqual(
      types,
      ['GENERATOR', 'GENERATOR', 'ROTATE', 'TWIST', 'EOF'],
      'Correctly tokenizes keywords',
    );
  });

  runTest('Lexer: tokenize class sigil', () => {
    const tokens = tokenize('c42 c0 c95');
    assertEqual(tokens[0].type, 'CLASS', 'c42 is CLASS');
    assertEqual(tokens[0].value, 'c42', 'c42 value is correct');
    assertEqual(tokens[2].value, 'c95', 'c95 value is correct');
  });

  runTest('Lexer: tokenize numbers', () => {
    const tokens = tokenize('123 0 47');
    const types = tokens.map((t) => t.type);
    assertArrayEqual(types, ['NUMBER', 'NUMBER', 'NUMBER', 'EOF'], 'Correctly tokenizes numbers');
  });

  runTest('Lexer: tokenize a full expression', () => {
    const tokens = tokenize('R+1@ (copy@c05 . evaluate@c21)');
    const types = tokens.map((t) => t.type);
    const expected = [
      'ROTATE',
      'PLUS',
      'NUMBER',
      'AT',
      'LPAREN',
      'GENERATOR',
      'AT',
      'CLASS',
      'DOT',
      'GENERATOR',
      'AT',
      'CLASS',
      'RPAREN',
      'EOF',
    ];
    assertArrayEqual(types, expected, 'Full expression tokenized correctly');
  });

  runTest('Lexer: skip whitespace and comments', () => {
    const tokens = tokenize('mark  // comment\n @ c0');
    const types = tokens.map((t) => t.type);
    assertArrayEqual(
      types,
      ['GENERATOR', 'AT', 'CLASS', 'EOF'],
      'Whitespace and comments are skipped',
    );
  });

  runTest('Lexer: handles invalid characters', () => {
    assertThrows(() => tokenize('$'), 'Should throw on invalid char', "unexpected '$'");
  });

  runTest('Lexer: handles empty input', () => {
    const tokens = tokenize('');
    assertEqual(tokens.length, 1, 'Should only have EOF');
    assertEqual(tokens[0].type, 'EOF', 'Token should be EOF');
  });

  runTest('Lexer: handles only whitespace and comments', () => {
    const tokens = tokenize('  // comment \n\t // another');
    assertEqual(tokens.length, 1, 'Should only have EOF');
    assertEqual(tokens[0].type, 'EOF', 'Token should be EOF');
  });

  runTest('Lexer: handles identifiers with numbers as errors', () => {
    assertThrows(
      () => tokenize('mark1@c00'),
      'Should error on invalid identifier',
      "unexpected 'mark1'",
    );
  });

  runTest('Lexer: handles incomplete parallel operator as error', () => {
    assertThrows(() => tokenize('|'), 'Should error on single pipe', "unexpected '|'");
  });

  runTest('Lexer: handles class sigil with trailing letters as error', () => {
    assertThrows(
      () => tokenize('c42a'),
      "Should error on invalid identifier 'a' after class",
      "unexpected 'a'",
    );
  });

  console.log('\n✓ All lexer tests passed!\n');
}

// ============================================================================
// Parser Tests
// ============================================================================

function runParserTests(): void {
  console.log('Running Parser Unit Tests...\n');

  runTest('Parser: simple operation', () => {
    const ast = Atlas.parse('mark@c42');
    assertEqual(ast.kind, 'Par', 'Top level is parallel');
  });

  runTest('Parser: sequential composition', () => {
    const ast = Atlas.parse('copy@c01 . swap@c02');
    const par = ast as any;
    const seq = par.branches[0];
    assertEqual(seq.kind, 'Seq', 'Sequential composition parsed');
    assertEqual(seq.items.length, 2, 'Two items in sequence');
  });

  runTest('Parser: parallel composition', () => {
    const ast = Atlas.parse('mark@c01 || mark@c02');
    const par = ast as any;
    assertEqual(par.branches.length, 2, 'Two parallel branches');
  });

  runTest('Parser: grouped expression', () => {
    const ast = Atlas.parse('(mark@c01 . copy@c02)');
    const par = ast as any;
    const group = par.branches[0].items[0];
    assertEqual(group.kind, 'Group', 'Grouped expression parsed');
  });

  runTest('Parser: deeply nested groups', () => {
    const ast = Atlas.parse('(((mark@c01)))');
    const par = ast as any;
    const group1 = par.branches[0].items[0];
    assertEqual(group1.kind, 'Group', 'Outer group');
    const group2 = group1.body.branches[0].items[0];
    assertEqual(group2.kind, 'Group', 'Middle group');
    const group3 = group2.body.branches[0].items[0];
    assertEqual(group3.kind, 'Group', 'Inner group');
  });

  runTest('Parser: transform prefix', () => {
    const ast = Atlas.parse('R+1@mark@c05');
    assertEqual(ast.kind, 'Xform', 'Transform prefix detected');
    const xform = ast as any;
    assertEqual(xform.transform, { R: 1 }, 'Transform object is correct');
  });

  runTest('Parser: sigil with postfix transforms', () => {
    const ast = Atlas.parse('mark@c42^+3~@17') as any;
    const op = ast.branches[0].items[0];
    const sigil = op.sigil;
    assertEqual(sigil.twist, 3, 'Postfix twist parsed');
    assertEqual(sigil.mirror, true, 'Postfix mirror parsed');
    assertEqual(sigil.page, 17, 'Postfix page parsed');
  });

  runTest('Parser: complex expression', () => {
    const ast = Atlas.parse('R+2 T-3 ~@ (copy@c01 . swap@c02 || merge@c03)');
    assertEqual(ast.kind, 'Xform', 'Complex transform parsed');
    const xform = ast as any;
    assertEqual(xform.transform, { R: 2, T: -3, M: true }, 'Complex transform object is correct');
  });

  runTest('Parser: throws on syntax error', () => {
    assertThrows(
      () => Atlas.parse('mark@c01 .'),
      'Should throw on incomplete sequence',
      'Expected GENERATOR but got EOF',
    );
    assertThrows(
      () => Atlas.parse('(mark@c01'),
      'Should throw on mismatched parens',
      'Expected RPAREN but got EOF',
    );
  });

  runTest('Parser: throws on invalid generator', () => {
    assertThrows(
      () => Atlas.parse('invalid@c01'),
      'Should throw on invalid generator',
      "unexpected 'invalid'",
    );
  });

  runTest('Parser: throws on out-of-range class index', () => {
    assertThrows(
      () => Atlas.parse('mark@c96'),
      'Should throw on c96',
      'Class index 96 out of range',
    );
  });

  runTest('Parser: throws on out-of-range page index', () => {
    assertThrows(
      () => Atlas.parse('mark@c00@48'),
      'Should throw on page 48',
      'Page index 48 out of range',
    );
  });

  runTest('Parser: sequential composition is right-to-left (in evaluation)', () => {
    const ast = Atlas.parse('mark@c01 . copy@c02 . swap@c03') as any;
    const seq = ast.branches[0];
    assertEqual(seq.items.length, 3, 'Three items in sequence');
    assertEqual(seq.items[0].generator, 'mark', 'First item is mark');
    assertEqual(seq.items[1].generator, 'copy', 'Second item is copy');
    assertEqual(seq.items[2].generator, 'swap', 'Third item is swap');
  });

  runTest('Parser: operator precedence (dot over parallel)', () => {
    const ast = Atlas.parse('mark@c01 . copy@c02 || swap@c03 . merge@c04') as any;
    assertEqual(ast.branches.length, 2, 'Two parallel branches');
    assertEqual(ast.branches[0].items.length, 2, 'First branch is a sequence of 2');
    assertEqual(ast.branches[1].items.length, 2, 'Second branch is a sequence of 2');
  });

  runTest('Parser: throws on empty group', () => {
    assertThrows(
      () => Atlas.parse('()'),
      'Should throw on empty group',
      'Expected GENERATOR but got RPAREN',
    );
  });

  runTest('Parser: throws on missing @', () => {
    assertThrows(
      () => Atlas.parse('mark c01'),
      'Should throw on missing @',
      'Expected AT but got CLASS',
    );
  });

  runTest('Parser: throws on invalid transform syntax', () => {
    assertThrows(
      () => Atlas.parse('R+ @ mark@c00'),
      'Should throw on transform without number',
      'Expected NUMBER but got AT',
    );
  });

  runTest('Parser: sigil with partial postfix transforms', () => {
    const ast1 = Atlas.parse('mark@c42~') as any;
    assertEqual(ast1.branches[0].items[0].sigil.mirror, true, 'Mirror only is parsed');
    const ast2 = Atlas.parse('mark@c42^+3') as any;
    assertEqual(ast2.branches[0].items[0].sigil.twist, 3, 'Twist only is parsed');
    const ast3 = Atlas.parse('mark@c42@17') as any;
    assertEqual(ast3.branches[0].items[0].sigil.page, 17, 'Page only is parsed');
  });

  runTest('Parser: throws on malformed expression with unconsumed tokens', () => {
    // With the lexer fix, this tokenizes to [GEN, AT, CLASS, CLASS, EOF].
    // With the parser EOF check, it should fail after parsing the first op.
    // Before, this would have failed in the lexer on 'c02'.
    assertThrows(
      () => Atlas.parse('mark@c01 c02'),
      'Should throw on unconsumed tokens',
      'Expected EOF but got CLASS',
    );
  });

  console.log('\n✓ All parser tests passed!\n');
}

// ============================================================================
// Class System Tests
// ============================================================================

function runClassSystemTests(): void {
  console.log('Running Class System Unit Tests...\n');

  // FIX: Use 'as const' to ensure object literal properties have literal types,
  // matching the stricter SigilComponents type.
  runTest('Class: decodeByteToComponents', () => {
    const comp = AtlasClass.decodeByteToComponents(0x2a);
    assertEqual(comp, { h2: 0 as const, d: 2 as const, l: 5 as const }, '0x2A decodes correctly');
    const comp2 = AtlasClass.decodeByteToComponents(0xc0);
    assertEqual(comp2, { h2: 3 as const, d: 0 as const, l: 0 as const }, '0xC0 decodes correctly');
  });

  // FIX: Use 'as const' to ensure object literal properties have literal types,
  // matching the stricter SigilComponents type for the function argument.
  runTest('Class: componentsToClassIndex', () => {
    const index = AtlasClass.componentsToClassIndex({
      h2: 0 as const,
      d: 2 as const,
      l: 5 as const,
    });
    assertEqual(index, 21, 'c21 components to index');
  });

  runTest('Class: byteToClassIndex', () => {
    assertEqual(Atlas.classIndex(0x00), 0, '0x00 → class 0');
    assertEqual(Atlas.classIndex(0x01), 0, '0x01 → class 0');
  });

  // FIX: Use 'as const' to ensure object literal properties have literal types,
  // matching the stricter SigilComponents type.
  runTest('Class: decodeClassIndex', () => {
    const comp = AtlasClass.decodeClassIndex(21);
    assertEqual(
      comp,
      { h2: 0 as const, d: 2 as const, l: 5 as const },
      'c21 index decodes correctly',
    );
    assertThrows(
      () => AtlasClass.decodeClassIndex(96),
      'Should throw for class 96',
      'out of range',
    );
    assertThrows(
      () => AtlasClass.decodeClassIndex(-1),
      'Should throw for class -1',
      'out of range',
    );
  });

  // FIX: Use 'as const' to ensure object literal properties have literal types,
  // matching the stricter SigilComponents type for the function argument.
  runTest('Class: encodeComponentsToByte', () => {
    const byte = AtlasClass.encodeComponentsToByte({
      h2: 0 as const,
      d: 2 as const,
      l: 5 as const,
    });
    assertEqual(byte, 0x2a, 'c21 components encode to 0x2A');
  });

  runTest('Class: classIndexToCanonicalByte', () => {
    assertEqual(Atlas.canonicalByte(0), 0x00, 'Class 0 → 0x00');
    assertEqual(Atlas.canonicalByte(21), 0x2a, 'Class 21 → 0x2A');
  });

  // FIX: Use 'as const' to ensure object literal properties have literal types,
  // matching the stricter SigilComponents type.
  runTest('Class: getClassInfo', () => {
    const info = AtlasClass.getClassInfo(0x2a);
    assertEqual(info.classIndex, 21, 'Class index is correct');
    assertEqual(info.canonicalByte, 0x2a, 'Canonical byte is correct');
    assertEqual(
      info.components,
      { h2: 0 as const, d: 2 as const, l: 5 as const },
      'Components are correct',
    );
  });

  // FIX: Use 'as const' to ensure object literal properties have literal types,
  // matching the stricter SigilComponents type for the function argument.
  runTest('Class: applyRotation', () => {
    const comp = AtlasClass.applyRotation({ h2: 0 as const, d: 0 as const, l: 0 as const }, 1);
    assertEqual(comp.h2, 1, 'Rotation works');
    const comp2 = AtlasClass.applyRotation({ h2: 3 as const, d: 0 as const, l: 0 as const }, 1);
    assertEqual(comp2.h2, 0, 'Rotation wraps around');
    const comp3 = AtlasClass.applyRotation({ h2: 1 as const, d: 0 as const, l: 0 as const }, -1);
    assertEqual(comp3.h2, 0, 'Negative rotation works');
    const comp4 = AtlasClass.applyRotation({ h2: 0 as const, d: 0 as const, l: 0 as const }, -1);
    assertEqual(comp4.h2, 3, 'Negative rotation wraps around');
  });

  // FIX: Use 'as const' to ensure object literal properties have literal types,
  // matching the stricter SigilComponents type for the function argument.
  runTest('Class: applyTwist', () => {
    const comp = AtlasClass.applyTwist({ h2: 0 as const, d: 0 as const, l: 0 as const }, 3);
    assertEqual(comp.l, 3, 'Twist works');
    const comp2 = AtlasClass.applyTwist({ h2: 0 as const, d: 0 as const, l: 7 as const }, 1);
    assertEqual(comp2.l, 0, 'Twist wraps around');
    const comp3 = AtlasClass.applyTwist({ h2: 0 as const, d: 0 as const, l: 1 as const }, -1);
    assertEqual(comp3.l, 0, 'Negative twist works');
    const comp4 = AtlasClass.applyTwist({ h2: 0 as const, d: 0 as const, l: 0 as const }, -1);
    assertEqual(comp4.l, 7, 'Negative twist wraps around');
  });

  // FIX: Use 'as const' to ensure object literal properties have literal types,
  // matching the stricter SigilComponents type for the function argument.
  runTest('Class: applyMirror', () => {
    const comp0 = AtlasClass.applyMirror({ h2: 0 as const, d: 0 as const, l: 0 as const });
    assertEqual(comp0.d, 0, 'Mirror on d=0 is d=0');
    const comp1 = AtlasClass.applyMirror({ h2: 0 as const, d: 1 as const, l: 0 as const });
    assertEqual(comp1.d, 2, 'Mirror on d=1 is d=2');
    const comp2 = AtlasClass.applyMirror({ h2: 0 as const, d: 2 as const, l: 0 as const });
    assertEqual(comp2.d, 1, 'Mirror on d=2 is d=1');
  });

  // FIX: Use 'as const' to ensure object literal properties have literal types,
  // matching the stricter SigilComponents type for the function argument.
  runTest('Class: applyTransforms with combined transforms', () => {
    const comp = AtlasClass.applyTransforms(
      { h2: 0 as const, d: 1 as const, l: 0 as const },
      { R: 1, T: -1, M: true },
    );
    // h2: 0+1=1, d: 1->2, l: 0-1=7
    assertEqual(
      comp,
      { h2: 1 as const, d: 2 as const, l: 7 as const },
      'Combined transforms work correctly',
    );
  });

  runTest('Class: areEquivalent', () => {
    assertEqual(AtlasClass.areEquivalent(0x00, 0x01), true, '0x00 and 0x01 are equivalent');
    assertEqual(AtlasClass.areEquivalent(0x00, 0x30), true, '0x00 and 0x30 are equivalent');
    assertEqual(AtlasClass.areEquivalent(0x00, 0x02), false, '0x00 and 0x02 are not equivalent');
  });

  runTest('Class: getEquivalenceClass size', () => {
    const class0 = Atlas.equivalenceClass(0);
    assertEqual(class0.length > 1, true, 'Class 0 has multiple members');
  });

  // FIX: Use 'as const' to ensure object literal properties have literal types,
  // matching the stricter SigilComponents type.
  runTest('Class: formatting functions', () => {
    const comp = { h2: 0 as const, d: 2 as const, l: 5 as const };
    assertEqual(
      AtlasClass.formatComponents(comp),
      '(h₂=0, d=2, ℓ=5)',
      'formatComponents is correct',
    );
    assertEqual(AtlasClass.formatModality(0), '•', 'formatModality for 0 is correct');
    assertEqual(AtlasClass.formatModality(1), '▲', 'formatModality for 1 is correct');
    assertEqual(AtlasClass.formatModality(2), '▼', 'formatModality for 2 is correct');
    const info = Atlas.classInfo(0x2a);
    assertEqual(
      AtlasClass.formatClassInfo(info),
      'c21 (h₂=0, d=2, ℓ=5) → 0x2A',
      'formatClassInfo is correct',
    );
  });

  runTest('Class: decodeByteToComponents with (b4,b5)=(1,1) fallback', () => {
    const comp = AtlasClass.decodeByteToComponents(0x30); // 00110000
    assertEqual(comp.d, 0, '(1,1) modality falls back to d=0');
  });

  // FIX: Use 'as const' to ensure object literal properties have literal types.
  runTest('Class: applyRotation with full wrap', () => {
    const comp = AtlasClass.applyRotation({ h2: 1 as const, d: 0 as const, l: 0 as const }, 4);
    assertEqual(comp.h2, 1, 'Rotation by 4 is a no-op');
  });

  // FIX: Use 'as const' to ensure object literal properties have literal types.
  runTest('Class: applyTwist with full wrap', () => {
    const comp = AtlasClass.applyTwist({ h2: 0 as const, d: 0 as const, l: 3 as const }, 8);
    assertEqual(comp.l, 3, 'Twist by 8 is a no-op');
  });

  runTest('Class: getEquivalenceClass exact members', () => {
    const class0 = Atlas.equivalenceClass(0);
    assertArrayEqual(class0, [0x00, 0x01, 0x30, 0x31], 'Class 0 has exactly 4 members');
  });

  console.log('\n✓ All class system tests passed!\n');
}

// ============================================================================
// Evaluator Tests
// ============================================================================

function runEvaluatorTests(): void {
  console.log('Running Evaluator Unit Tests...\n');

  runTest('Evaluator: Literal backend evaluates sequence', () => {
    const result = Atlas.evaluateBytes('mark@c01 . copy@c02');
    assertArrayEqual(result.bytes, [0x04, 0x02], 'Sequence bytes are correct');
  });

  runTest('Evaluator: Literal backend with complex transforms', () => {
    // R+1 T-1 M @ c1 (h2=0,d=0,l=1) -> h2=1, d=0, l=0 -> class 24 -> 0x40
    const result = Atlas.evaluateBytes('R+1 T-1 ~@ mark@c01');
    assertArrayEqual(result.bytes, [0x40], 'Complex prefix transform works');
  });

  runTest('Evaluator: Literal backend with postfix and prefix', () => {
    // R+1@ (mark@c00^+1) -> R+1 @ T+1 @ c00
    // T+1 -> c0(h2=0,d=0,l=0) -> c1 (h2=0, d=0, l=1)
    // R+1 -> c1 -> c25 (h2=1, d=0, l=1) -> 0x42
    const result = Atlas.evaluateBytes('R+1@mark@c00^+1');
    assertArrayEqual(result.bytes, [0x42], 'Prefix and postfix transforms combine correctly');
  });

  runTest('Evaluator: Operational backend produces words for all generators', () => {
    assertArrayEqual(Atlas.evaluateWords('mark@c00').words, ['mark'], 'mark word');
    assertArrayEqual(Atlas.evaluateWords('copy@c05').words, ['copy[d=0]'], 'copy word');
    assertArrayEqual(Atlas.evaluateWords('swap@c72').words, ['swap'], 'swap word');
    assertArrayEqual(Atlas.evaluateWords('merge@c13').words, ['merge[d=1]'], 'merge word');
    assertArrayEqual(Atlas.evaluateWords('split@c20').words, ['split[ℓ=4]'], 'split word');
    assertArrayEqual(Atlas.evaluateWords('quote@c30').words, ['quote[ℓ=6]'], 'quote word');
    assertArrayEqual(
      Atlas.evaluateWords('evaluate@c21').words,
      ['phase[h₂=0]', 'evaluate'],
      'evaluate words',
    );
  });

  runTest('Evaluator: Operational backend for sequence', () => {
    const result = Atlas.evaluateWords('copy@c05 . evaluate@c40');
    const expected = ['phase[h₂=1]', 'evaluate', 'copy[d=0]'];
    assertArrayEqual(result.words, expected, 'Operational words are correct for sequence');
  });

  runTest('Evaluator: Operational backend for parallel composition', () => {
    const result = Atlas.evaluateWords('mark@c01 || mark@c02');
    const expected = ['⊗_begin', 'mark', '⊗_sep', 'mark', '⊗_end'];
    assertArrayEqual(result.words, expected, 'Parallel composition words are correct');
  });

  runTest('Evaluator: Operational backend handles transforms', () => {
    const result = Atlas.evaluateWords('R+1@mark@c00');
    const expected = ['→ρ[1]', 'mark', '←ρ[1]'];
    assertArrayEqual(result.words, expected, 'Operational words for R transform are correct');
  });

  runTest('Evaluator: formatBytes helper', () => {
    const formatted = Atlas.formatBytes([0x2a, 0x0a]);
    assertEqual(formatted, '0x2A 0x0A', 'formatBytes works correctly');
  });

  runTest('Evaluator: formatAddresses helper', () => {
    const formatted = Atlas.formatAddresses([4398, 0]);
    assertEqual(formatted, '4398, 0', 'formatAddresses works correctly');
  });

  runTest('Evaluator: formatWords helper', () => {
    const formatted = Atlas.formatWords(['word1', 'word2'], 2);
    assertEqual(formatted, '  word1\n  word2', 'formatWords works correctly');
  });

  runTest('Evaluator: combineTransforms logic via evaluation', () => {
    const result = Atlas.evaluateBytes('R+1@ (T-1 ~@ mark@c00)');
    assertEqual(
      result.bytes[0],
      Atlas.canonicalByte(31),
      'Outer and inner transforms combine correctly',
    );

    const mirror_xor = Atlas.evaluateBytes('~@(~@mark@c13)');
    const no_mirror = Atlas.evaluateBytes('mark@c13');
    assertEqual(mirror_xor.bytes[0], no_mirror.bytes[0], 'Double mirror cancels out');
  });

  runTest('Evaluator: deeply nested structure evaluation', () => {
    const expr = 'R+1@ (copy@c01 . (swap@c02 || mark@c03^+1) . merge@c04)';
    const result = Atlas.evaluate(expr);
    assertEqual(
      result.literal.bytes.length,
      4,
      'Deeply nested expression has correct number of bytes',
    );
    assertEqual(
      result.operational.words.length > 5,
      true,
      'Deeply nested expression has operational words',
    );
  });

  console.log('\n✓ All evaluator tests passed!\n');
}

// ============================================================================
// Belt System Tests
// ============================================================================

function runBeltTests(): void {
  console.log('Running Belt System Unit Tests...\n');

  runTest('Belt: address computation', () => {
    const addr = Atlas.beltAddress(0, 0);
    assertEqual(addr.address, 0, 'Page 0, byte 0 → address 0');
    const addr2 = Atlas.beltAddress(1, 0);
    assertEqual(addr2.address, 256, 'Page 1, byte 0 → address 256');
    const addr3 = Atlas.beltAddress(47, 255);
    assertEqual(addr3.address, 12287, 'Page 47, byte 255 → address 12287');
  });

  runTest('Belt: address decomposition', () => {
    const decomp = Atlas.decodeBeltAddress(256);
    assertEqual(decomp.page, 1, 'Address 256 → page 1');
    assertEqual(decomp.byte, 0, 'Address 256 → byte 0');
    const decomp2 = Atlas.decodeBeltAddress(12287);
    assertEqual(decomp2.page, 47, 'Address 12287 → page 47');
    assertEqual(decomp2.byte, 255, 'Address 12287 → byte 255');
  });

  runTest('Belt: address range validation', () => {
    assertThrows(() => Atlas.beltAddress(48, 0), 'Should throw for page 48', 'out of range');
    assertThrows(
      () => Atlas.decodeBeltAddress(12288),
      'Should throw for address 12288',
      'out of range',
    );
  });

  console.log('\n✓ All belt system tests passed!\n');
}

// ============================================================================
// Integration Tests
// ============================================================================

function runIntegrationTests(): void {
  console.log('Running Integration Tests...\n');

  runTest('Integration: Complete workflow: parse → evaluate → format', () => {
    const source = 'evaluate@c21 . copy@c05';
    const output = Atlas.prettyPrint(source);
    assertEqual(output.includes('0x2A'), true, 'Output contains expected bytes');
  });

  runTest('Integration: Round-trip: class → byte → class', () => {
    for (let i = 0; i < 96; i++) {
      const byte = Atlas.canonicalByte(i);
      const classIdx = Atlas.classIndex(byte);
      assertEqual(classIdx, i, `Class ${i} round-trips correctly`);
    }
  });

  runTest('Integration: Transform preservation', () => {
    const result1 = Atlas.evaluateBytes('R+1@mark@c00');
    const result2 = Atlas.evaluateBytes('mark@c24'); // c00 + 1 quadrant = c24
    assertEqual(
      Atlas.classIndex(result1.bytes[0]),
      Atlas.classIndex(result2.bytes[0]),
      'R+1@c00 should equal c24',
    );
  });

  runTest('Integration: Prefix and postfix transforms are equivalent', () => {
    // R+1 @ T+2 @ M @ c5
    const prefix = Atlas.evaluateBytes('R+1 T+2 ~@ mark@c05');
    // R+1 @ (mark@c05^+2~)
    const mixed = Atlas.evaluateBytes('R+1@ mark@c05^+2~');

    // Calculate expected target class manually:
    // c5 (h2=0,d=0,l=5) -> Postfix T+2, M -> d=0, l=7 -> c7(h2=0,d=0,l=7)
    // Then Prefix R+1 on c7 -> h2=1 -> c31(h2=1,d=0,l=7)
    const targetByte = Atlas.canonicalByte(31);

    assertArrayEqual(prefix.bytes, [targetByte], 'Prefix result is correct');
    assertArrayEqual(mixed.bytes, [targetByte], 'Mixed pre/post result is correct');
  });

  runTest('Integration: Introspection functions return correct counts', () => {
    const allClasses = Atlas.allClasses();
    assertEqual(allClasses.length, 96, 'allClasses() returns 96 classes');
    const byteMapping = Atlas.byteClassMapping();
    assertEqual(byteMapping.length, 256, 'byteClassMapping() returns 256 mappings');
  });

  runTest('Integration: Kitchen sink expression', () => {
    const expr = 'R-1 T+5 ~@ ( (copy@c05 . evaluate@c21^+1~@2) || (swap@c72 . mark@c00) )';
    try {
      const result = Atlas.evaluate(expr);
      assertEqual(
        result.literal.bytes.length,
        4,
        'Kitchen sink literal evaluation has correct byte count',
      );
      assertEqual(
        result.literal.addresses?.length,
        1,
        'Kitchen sink literal evaluation has correct address count',
      );
      assertEqual(
        result.operational.words.length > 5,
        true,
        'Kitchen sink operational evaluation has words',
      );
    } catch (e: any) {
      throw new Error(`Kitchen sink expression failed to evaluate: ${e.message}`);
    }
  });

  console.log('\n✓ All integration tests passed!\n');
}

// ============================================================================
// D-Transform Tests
// ============================================================================

function testDTransformBasics(): void {
  console.log('Running D-Transform Basic Tests...\n');

  runTest('D+1 rotates modality 0→1', () => {
    // c0 (h₂=0, d=0, ℓ=0) → D+1 → c8 (h₂=0, d=1, ℓ=0)
    const result = Atlas.applyDTransform(0, 1);
    assertEqual(result.newClass, 8, 'c0 D+1 should be c8');
    assertEqual(result.transformation.d_old, 0, 'd_old should be 0');
    assertEqual(result.transformation.d_new, 1, 'd_new should be 1');
  });

  runTest('D+1 rotates modality 1→2', () => {
    // c8 (h₂=0, d=1, ℓ=0) → D+1 → c16 (h₂=0, d=2, ℓ=0)
    const result = Atlas.applyDTransform(8, 1);
    assertEqual(result.newClass, 16, 'c8 D+1 should be c16');
    assertEqual(result.transformation.d_new, 2, 'd_new should be 2');
  });

  runTest('D+1 rotates modality 2→0', () => {
    // c16 (h₂=0, d=2, ℓ=0) → D+1 → c0 (h₂=0, d=0, ℓ=0)
    const result = Atlas.applyDTransform(16, 1);
    assertEqual(result.newClass, 0, 'c16 D+1 should be c0');
    assertEqual(result.transformation.d_new, 0, 'd_new should be 0');
  });

  runTest('D+2 is same as D-1', () => {
    const plus2 = Atlas.applyDTransform(8, 2);
    const minus1 = Atlas.applyDTransform(8, -1);
    assertEqual(plus2.newClass, minus1.newClass, 'D+2 should equal D-1');
  });

  runTest('D+3 is identity (period 3)', () => {
    for (let c = 0; c < 96; c++) {
      const result = Atlas.applyDTransform(c, 3);
      assertEqual(result.newClass, c, `D+3 should be identity for c${c}`);
    }
  });

  runTest('D+6 is identity (double period)', () => {
    const result = Atlas.applyDTransform(21, 6);
    assertEqual(result.newClass, 21, 'D+6 should be identity');
  });

  runTest('D-transform preserves h₂', () => {
    for (let c = 0; c < 96; c++) {
      const info = Atlas.classInfo(Atlas.canonicalByte(c));
      const result = Atlas.applyDTransform(c, 1);
      const newInfo = Atlas.classInfo(Atlas.canonicalByte(result.newClass));
      assertEqual(newInfo.components.h2, info.components.h2, `h₂ should be preserved for c${c}`);
    }
  });

  runTest('D-transform preserves ℓ', () => {
    for (let c = 0; c < 96; c++) {
      const info = Atlas.classInfo(Atlas.canonicalByte(c));
      const result = Atlas.applyDTransform(c, 1);
      const newInfo = Atlas.classInfo(Atlas.canonicalByte(result.newClass));
      assertEqual(newInfo.components.l, info.components.l, `ℓ should be preserved for c${c}`);
    }
  });

  console.log('\n✓ All D-transform basic tests passed!\n');
}

function testTrialityOrbits(): void {
  console.log('Running Triality Orbit Tests...\n');

  runTest('triality orbit contains 3 classes', () => {
    const orbit = Atlas.getTrialityOrbit(0);
    assertEqual(orbit.classes.length, 3, 'Orbit should have 3 classes');
  });

  runTest('triality orbit for c0 is [0, 8, 16]', () => {
    const orbit = Atlas.getTrialityOrbit(0);
    assertArrayEqual(orbit.classes, [0, 8, 16], 'c0 orbit should be [0, 8, 16]');
  });

  runTest('triality orbit for c21 is [5, 13, 21]', () => {
    const orbit = Atlas.getTrialityOrbit(21);
    assertArrayEqual(orbit.classes, [5, 13, 21], 'c21 orbit should be [5, 13, 21]');
  });

  runTest('orbit is same for all 3 members', () => {
    const orbit1 = Atlas.getTrialityOrbit(0);
    const orbit2 = Atlas.getTrialityOrbit(8);
    const orbit3 = Atlas.getTrialityOrbit(16);
    assertArrayEqual(orbit1.classes, orbit2.classes, 'Orbits should match');
    assertArrayEqual(orbit2.classes, orbit3.classes, 'Orbits should match');
  });

  runTest('base coordinates match class h₂ and ℓ', () => {
    const orbit = Atlas.getTrialityOrbit(21);
    const info = Atlas.classInfo(Atlas.canonicalByte(21));
    assertEqual(orbit.baseCoordinates.h2, info.components.h2, 'h₂ should match');
    assertEqual(orbit.baseCoordinates.l, info.components.l, 'ℓ should match');
  });

  runTest('all 32 orbits generated', () => {
    const orbits = Atlas.getAllTrialityOrbits();
    assertEqual(orbits.length, 32, 'Should have 32 orbits');
  });

  runTest('all 96 classes covered by orbits', () => {
    const orbits = Atlas.getAllTrialityOrbits();
    const allClasses = new Set<number>();
    for (const orbit of orbits) {
      for (const c of orbit.classes) {
        allClasses.add(c);
      }
    }
    assertEqual(allClasses.size, 96, 'All 96 classes should be covered');
  });

  runTest('no class appears in multiple orbits', () => {
    const orbits = Atlas.getAllTrialityOrbits();
    const seen = new Set<number>();
    for (const orbit of orbits) {
      for (const c of orbit.classes) {
        if (seen.has(c)) {
          throw new Error(`Class ${c} appears in multiple orbits`);
        }
        seen.add(c);
      }
    }
  });

  console.log('\n✓ All triality orbit tests passed!\n');
}

function testDTransformParsing(): void {
  console.log('Running D-Transform Parsing Tests...\n');

  runTest('parse D+1 prefix transform', () => {
    const ast = Atlas.parse('D+1@ mark@c0');
    if (ast.kind !== 'Xform') {
      throw new Error('Expected Xform node');
    }
    assertEqual(ast.transform.D, 1, 'D should be 1');
  });

  runTest('parse D-1 prefix transform', () => {
    const ast = Atlas.parse('D-1@ mark@c0');
    if (ast.kind !== 'Xform') {
      throw new Error('Expected Xform node');
    }
    assertEqual(ast.transform.D, -1, 'D should be -1');
  });

  runTest('parse combined R+2 D+1 T+3', () => {
    const ast = Atlas.parse('R+2 D+1 T+3@ mark@c0');
    if (ast.kind !== 'Xform') {
      throw new Error('Expected Xform node');
    }
    assertEqual(ast.transform.R, 2, 'R should be 2');
    assertEqual(ast.transform.D, 1, 'D should be 1');
    assertEqual(ast.transform.T, 3, 'T should be 3');
  });

  runTest('parse D+1 T+2 (no R)', () => {
    const ast = Atlas.parse('D+1 T+2@ mark@c0');
    if (ast.kind !== 'Xform') {
      throw new Error('Expected Xform node');
    }
    assertEqual(ast.transform.D, 1, 'D should be 1');
    assertEqual(ast.transform.T, 2, 'T should be 2');
    assertEqual(ast.transform.R, undefined, 'R should be undefined');
  });

  runTest('parse D postfix syntax c21^D+1', () => {
    const ast = Atlas.parse('mark@c21^D+1');
    if (
      ast.kind !== 'Par' ||
      ast.branches[0].kind !== 'Seq' ||
      ast.branches[0].items[0].kind !== 'Op'
    ) {
      throw new Error('Expected operation node');
    }
    const sigil = ast.branches[0].items[0].sigil;
    assertEqual(sigil.triality, 1, 'triality should be 1');
  });

  console.log('\n✓ All D-transform parsing tests passed!\n');
}

function testDTransformEvaluation(): void {
  console.log('Running D-Transform Evaluation Tests...\n');

  runTest('evaluate D+1@ mark@c21 to bytes', () => {
    // c21 (h₂=0, d=2, ℓ=5) → D+1 → c5 (h₂=0, d=0, ℓ=5)
    const result = Atlas.evaluateBytes('D+1@ mark@c21');
    const classIndex = Atlas.classIndex(result.bytes[0]);
    assertEqual(classIndex, 5, 'Should transform to c5');
  });

  runTest('evaluate D+2@ mark@c21 to bytes', () => {
    // c21 (h₂=0, d=2, ℓ=5) → D+2 → c13 (h₂=0, d=1, ℓ=5)
    const result = Atlas.evaluateBytes('D+2@ mark@c21');
    const classIndex = Atlas.classIndex(result.bytes[0]);
    assertEqual(classIndex, 13, 'Should transform to c13');
  });

  runTest('evaluate D-1@ mark@c21 to bytes', () => {
    // D-1 should equal D+2
    const result = Atlas.evaluateBytes('D-1@ mark@c21');
    const classIndex = Atlas.classIndex(result.bytes[0]);
    assertEqual(classIndex, 13, 'D-1 should equal D+2');
  });

  runTest('evaluate R+1 D+1@ mark@c0 to bytes', () => {
    // c0 (h₂=0, d=0, ℓ=0) → D+1 → c8 (h₂=0, d=1, ℓ=0) → R+1 → c32 (h₂=1, d=1, ℓ=0)
    const result = Atlas.evaluateBytes('R+1 D+1@ mark@c0');
    const classIndex = Atlas.classIndex(result.bytes[0]);
    assertEqual(classIndex, 32, 'Combined R+1 D+1 should give c32');
  });

  runTest('evaluate D+1 T+1@ mark@c0 to bytes', () => {
    // c0 (h₂=0, d=0, ℓ=0) → D+1 → c8 (h₂=0, d=1, ℓ=0) → T+1 → c9 (h₂=0, d=1, ℓ=1)
    const result = Atlas.evaluateBytes('D+1 T+1@ mark@c0');
    const classIndex = Atlas.classIndex(result.bytes[0]);
    assertEqual(classIndex, 9, 'Combined D+1 T+1 should give c9');
  });

  runTest('evaluate combined R+2 D+1 T+3@ mark@c0', () => {
    const result = Atlas.evaluateBytes('R+2 D+1 T+3@ mark@c0');
    assertEqual(result.bytes.length, 1, 'Should have 1 byte');
  });

  runTest('operational words include D-transform markers', () => {
    const result = Atlas.evaluateWords('D+1@ mark@c0');
    const hasTrialityMarker = result.words.some((w) => w.includes('δ'));
    assertEqual(hasTrialityMarker, true, 'Should have δ marker in operational words');
  });

  runTest('lexer recognizes D token', () => {
    const tokens = tokenize('D+1');
    assertEqual(tokens[0].type, 'TRIALITY', 'First token should be TRIALITY');
    assertEqual(tokens[0].value, 'D', 'Token value should be D');
  });

  console.log('\n✓ All D-transform evaluation tests passed!\n');
}

// ============================================================================
// Run All Tests
// ============================================================================

function runAllTests(): void {
  console.log('='.repeat(60));
  console.log('Atlas Test Suite');
  console.log('='.repeat(60));
  console.log();

  try {
    runSpecificationTests();
    runLexerTests();
    runParserTests();
    runClassSystemTests();
    runEvaluatorTests();
    runBeltTests();
    runIntegrationTests();
    testDTransformBasics();
    testTrialityOrbits();
    testDTransformParsing();
    testDTransformEvaluation();

    // v0.3.0: SGA Tests
    console.log('\n');
    console.log('='.repeat(60));
    console.log('v0.3.0: SGA (Sigmatics Geometric Algebra) Tests');
    console.log('='.repeat(60));
    console.log();

    runGroupAlgebraTests();
    runSgaLawsTests();
    runBridgeTests();
    runBugFixTests();

    console.log('='.repeat(60));
    console.log('✓ ALL TESTS PASSED (including v0.3.0 SGA tests and v0.3.1 bug fixes)');
    console.log('='.repeat(60));
  } catch (error: any) {
    console.log('\n' + '='.repeat(60));
    console.log('✗ TESTS FAILED');
    console.log('='.repeat(60));
    throw error;
  }
}

// Run if executed directly
if (require.main === module) {
  runAllTests();
}
