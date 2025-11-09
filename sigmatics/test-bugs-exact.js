#!/usr/bin/env node
/**
 * Test exact scenarios from bug report
 */

const { Atlas } = require('./packages/core/dist/index.js');

console.log('Testing Exact Bug Report Scenarios\n');
console.log('='.repeat(60));

// The bug report shows: z4Power(gen, 4)
// But z4Power only takes one parameter: z4Power(k)
// Maybe they meant something else?
console.log('\nBUG-001 Scenario 1: Direct z4Power function');
console.log('-'.repeat(60));
try {
  const gen = Atlas.SGA.z4Generator();
  console.log('z4Generator():', JSON.stringify(gen));

  // This should fail since z4Power only takes 1 param
  console.log('Calling z4Power(gen, 4)...');
  const result = Atlas.SGA.z4Power(gen, 4);
  console.log('Result:', JSON.stringify(result));
} catch (e) {
  console.log('ERROR (expected):', e.message);
}

// Correct way
console.log('\nCorrect way: z4Power(4)');
const r4_correct = Atlas.SGA.z4Power(4);
console.log('z4Power(4):', JSON.stringify(r4_correct));

// Maybe they meant using multiply repeatedly?
console.log('\nManual multiplication: gen * gen * gen * gen');
let gen = Atlas.SGA.z4Generator();
console.log('Start:', JSON.stringify(gen));
gen = Atlas.SGA.z4Multiply(gen, Atlas.SGA.z4Generator());
console.log('gen^2:', JSON.stringify(gen));
gen = Atlas.SGA.z4Multiply(gen, Atlas.SGA.z4Generator());
console.log('gen^3:', JSON.stringify(gen));
gen = Atlas.SGA.z4Multiply(gen, Atlas.SGA.z4Generator());
console.log('gen^4:', JSON.stringify(gen));

// BUG-015: Using R(1) as element in sgaMultiply
console.log('\n\nBUG-015: Transform as element');
console.log('-'.repeat(60));
try {
  const element = Atlas.SGA.lift(21);

  // The bug report says: "sgaMultiply(R(1), element)"
  // R is a function wrapper, not an element
  console.log('Calling R(1)...');
  const r1_result = Atlas.SGA.R(1);
  console.log('R(1) returns:', r1_result ? typeof r1_result : 'undefined');

  if (r1_result) {
    console.log('Calling sgaMultiply(R(1), element)...');
    const product = Atlas.SGA.sgaMultiply(r1_result, element);
    console.log('Result:', product ? 'OK' : 'FAILED');
  }
} catch (e) {
  console.log('ERROR:', e.message);
  console.log('Stack:', e.stack);
}

// Maybe they meant R(element) applied to a number?
console.log('\nTrying R(1) where 1 is treated as a number...');
try {
  const element = 1; // Just a number
  const result = Atlas.SGA.R(element);
  console.log('R(1):', result ? 'OK' : 'FAILED');
} catch (e) {
  console.log('ERROR:', e.message);
}

// The convenience wrapper expects an SGA element
console.log('\nCorrect: R(sgaElement)');
const elem = Atlas.SGA.lift(21);
const transformed = Atlas.SGA.R(elem);
console.log('R(lifted element):', transformed ? 'OK' : 'FAILED');

console.log('\n' + '='.repeat(60));
