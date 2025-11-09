/**
 * Basic Operations Example
 * 
 * This example demonstrates basic hologram-ffi operations including version checking,
 * executor phase management, and simple mathematical operations.
 */

import * as hg from '../src/index';

console.log('🚀 Hologram FFI - Basic Operations Example');
console.log('==========================================');

// Get version information
console.log('\n📋 Version Information:');
console.log(`Hologram FFI Version: ${hg.getVersion()}`);

// Check executor phase
console.log('\n🔄 Executor Phase Management:');
const currentPhase = hg.getExecutorPhase();
console.log(`Current executor phase: ${currentPhase}`);

// Advance phase
hg.advanceExecutorPhase(1);
const newPhase = hg.getExecutorPhase();
console.log(`Phase after advancing by 1: ${newPhase}`);

// Atlas state management
console.log('\n🌍 Atlas State Management:');
const atlasPhase = hg.atlasPhase();
console.log(`Current Atlas phase: ${atlasPhase}`);

// Advance Atlas phase
hg.atlasAdvancePhase(2);
const newAtlasPhase = hg.atlasPhase();
console.log(`Atlas phase after advancing by 2: ${newAtlasPhase}`);

// Get resonance values
console.log('\n🎵 Resonance Values:');
for (let i = 0; i < 5; i++) {
  const resonance = hg.atlasResonanceAt(i);
  console.log(`Resonance at class ${i}: ${resonance.toFixed(4)}`);
}

// Get resonance snapshot
const resonanceSnapshot = hg.atlasResonanceSnapshot();
console.log(`Resonance snapshot: ${resonanceSnapshot}`);

// Mathematical operations
console.log('\n🧮 Mathematical Operations:');
const vectorLength = 1000;

console.log('Performing vector operations...');
hg.vectorAddF32(vectorLength);
hg.vectorSubF32(vectorLength);
hg.vectorMulF32(vectorLength);
hg.vectorDivF32(vectorLength);
hg.vectorAbsF32(vectorLength);
hg.vectorNegF32(vectorLength);
hg.vectorReluF32(vectorLength);

console.log('Performing reduction operations...');
const sum = hg.reduceSumF32(vectorLength);
const max = hg.reduceMaxF32(vectorLength);
const min = hg.reduceMinF32(vectorLength);

console.log(`Reduction results for length ${vectorLength}:`);
console.log(`  Sum: ${sum}`);
console.log(`  Max: ${max}`);
console.log(`  Min: ${min}`);

// Activation functions
console.log('\n🎯 Activation Functions:');
hg.sigmoidF32(vectorLength);
hg.tanhF32(vectorLength);
hg.softmaxF32(vectorLength);

// Linear algebra operations
console.log('\n📐 Linear Algebra Operations:');
const m = 100, n = 50, k = 75;
console.log(`Performing GEMM operation: ${m}x${k} * ${k}x${n} = ${m}x${n}`);
hg.gemmF32(m, n, k);

console.log(`Performing matrix-vector multiplication: ${m}x${n}`);
hg.matvecF32(m, n);

// Loss functions
console.log('\n📊 Loss Functions:');
const lossLength = 1000;
const mseLoss = hg.mseLossF32(lossLength);
const crossEntropyLoss = hg.crossEntropyLossF32(lossLength);

console.log(`Loss functions for length ${lossLength}:`);
console.log(`  MSE Loss: ${mseLoss}`);
console.log(`  Cross-entropy Loss: ${crossEntropyLoss}`);

// Additional math operations
console.log('\n🔢 Additional Math Operations:');
hg.vectorMinF32(vectorLength);
hg.vectorMaxF32(vectorLength);
hg.scalarAddF32(2.5, vectorLength);
hg.scalarMulF32(1.5, vectorLength);
hg.geluF32(vectorLength);

// Boundary operations
console.log('\n🔲 Boundary Operations:');
const width = 32, height = 32;
console.log(`Performing boundary transpose: ${width}x${height}`);
hg.transposeBoundaryF32(width, height);

console.log('\n✅ Basic operations completed successfully!');
