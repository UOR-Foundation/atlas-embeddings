#!/usr/bin/env node
/**
 * Test script to reproduce reported bugs
 */

const { Atlas } = require('./packages/core/dist/index.js');

console.log('Testing Bug Reports\n');
console.log('='.repeat(60));

// BUG-001: Z4 Group Algebra Power Wrapping Failure
console.log('\nBUG-001: Z4 Power Wrapping');
console.log('-'.repeat(60));
try {
  // Create Z4 generator r = r^1
  const r = Atlas.SGA.createRank1Basis(1, 0, 0); // r^1 ⊗ 1 ⊗ τ^0
  console.log('Generator r:', JSON.stringify(r.z4));

  // Raise to 4th power using sgaPower
  const r4 = Atlas.SGA.sgaPower(r, 4);
  console.log('r^4 =', JSON.stringify(r4.z4));
  console.log('Expected: {"coefficients":[1,0,0,0]}');
  console.log('Match:', JSON.stringify(r4.z4) === '{"coefficients":[1,0,0,0]}');
} catch (e) {
  console.log('ERROR:', e.message);
}

// BUG-004: Z3 Group Algebra Power Wrapping Failure
console.log('\nBUG-004: Z3 Power Wrapping');
console.log('-'.repeat(60));
try {
  // Create Z3 generator τ = τ^1
  const tau = Atlas.SGA.createRank1Basis(0, 1, 0); // r^0 ⊗ 1 ⊗ τ^1
  console.log('Generator τ:', JSON.stringify(tau.z3));

  // Raise to 3rd power
  const tau3 = Atlas.SGA.sgaPower(tau, 3);
  console.log('τ^3 =', JSON.stringify(tau3.z3));
  console.log('Expected: {"coefficients":[1,0,0]}');
  console.log('Match:', JSON.stringify(tau3.z3) === '{"coefficients":[1,0,0]}');
} catch (e) {
  console.log('ERROR:', e.message);
}

// BUG-015: Transform Function Application Crash
console.log('\nBUG-015: Transform Function Application');
console.log('-'.repeat(60));
try {
  const element = Atlas.SGA.lift(21);
  console.log('Lifted element:', element ? 'OK' : 'UNDEFINED');

  // Try applying R transform directly
  const r1 = Atlas.SGA.createRank1Basis(1, 0, 0); // r^1
  console.log('R(1) element:', r1 ? 'OK' : 'UNDEFINED');

  const result = Atlas.SGA.sgaMultiply(r1, element);
  console.log('sgaMultiply result:', result ? 'OK' : 'UNDEFINED');
  console.log('Result has grades:', result && result.clifford && result.clifford.grades ? 'YES' : 'NO');
} catch (e) {
  console.log('ERROR:', e.message);
  console.log('Stack:', e.stack);
}

// BUG-009: Inconsistent Validation API Returns
console.log('\nBUG-009: Validation API Consistency');
console.log('-'.repeat(60));
try {
  const fullValidation = Atlas.SGA.validate();
  console.log('validate() returns:', Object.keys(fullValidation));
  console.log('Has allPassed:', 'allPassed' in fullValidation);
  console.log('Has summary:', 'summary' in fullValidation);

  const rValidation = Atlas.SGA.validateR();
  console.log('\nvalidateR() returns:', Array.isArray(rValidation) ? `Array[${rValidation.length}]` : typeof rValidation);
  console.log('Has allPassed:', rValidation && 'allPassed' in rValidation);
  console.log('Has summary:', rValidation && 'summary' in rValidation);

  if (Array.isArray(rValidation)) {
    console.log('First element:', rValidation[0] ? Object.keys(rValidation[0]) : 'none');
  }
} catch (e) {
  console.log('ERROR:', e.message);
}

// BUG-012: Octonion Alternativity Verification Crash
console.log('\nBUG-012: Octonion Alternativity Verification');
console.log('-'.repeat(60));
try {
  const x = Atlas.SGA.Octonion.randomOctonion();
  const y = Atlas.SGA.Octonion.randomOctonion();
  console.log('Created random octonions:', x && y ? 'OK' : 'FAILED');
  console.log('x has grades:', x && x.grades ? 'YES' : 'NO');
  console.log('y has grades:', y && y.grades ? 'YES' : 'NO');

  const result = Atlas.SGA.Octonion.verifyAlternativity(x, y);
  console.log('Alternativity result:', result);
} catch (e) {
  console.log('ERROR:', e.message);
  console.log('Stack:', e.stack);
}

// BUG-013: Octonion Norm Verification Crash
console.log('\nBUG-013: Octonion Norm Verification');
console.log('-'.repeat(60));
try {
  const x = Atlas.SGA.Octonion.randomOctonion();
  const y = Atlas.SGA.Octonion.randomOctonion();
  console.log('Created random octonions:', x && y ? 'OK' : 'FAILED');

  const result = Atlas.SGA.Octonion.verifyNormMultiplicativity(x, y);
  console.log('Norm multiplicativity result:', result);
} catch (e) {
  console.log('ERROR:', e.message);
  console.log('Stack:', e.stack);
}

console.log('\n' + '='.repeat(60));
