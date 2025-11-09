/**
 * Executor Management Example
 * 
 * This example demonstrates comprehensive executor management including creation,
 * buffer allocation, phase management, resonance tracking, and topology operations.
 */

import * as hg from '../src/index';

console.log('🚀 Hologram FFI - Executor Management Example');
console.log('=============================================');

// Create a new executor
console.log('\n🏗️ Creating Executor:');
const executorHandle = hg.newExecutor();
console.log(`Created executor with handle: ${executorHandle}`);

// Create executor with custom backend
console.log('\n🔧 Creating Executor with Custom Backend:');
const customExecutorHandle = hg.executorWithBackend('cpu');
console.log(`Created custom executor with handle: ${customExecutorHandle}`);

// Get executor phase
console.log('\n📊 Executor Phase Management:');
const phase = hg.executorPhase(executorHandle);
console.log(`Current executor phase: ${phase}`);

// Advance executor phase
hg.executorAdvancePhase(executorHandle, 5);
const newPhase = hg.executorPhase(executorHandle);
console.log(`Phase after advancing by 5: ${newPhase}`);

// Allocate buffers
console.log('\n💾 Buffer Allocation:');
const bufferSize = 1024;
const bufferHandle = hg.executorAllocateBuffer(executorHandle, bufferSize);
console.log(`Allocated buffer with handle: ${bufferHandle}, size: ${bufferSize}`);

// Try to allocate boundary buffer
console.log('\n🔲 Boundary Buffer Allocation:');
try {
  const boundaryBufferHandle = hg.executorAllocateBoundaryBuffer(executorHandle, 0, 32, 32);
  console.log(`Allocated boundary buffer with handle: ${boundaryBufferHandle}`);
  
  // Check buffer properties
  const isBoundary = hg.bufferIsBoundary(boundaryBufferHandle);
  const isLinear = hg.bufferIsLinear(boundaryBufferHandle);
  const elementSize = hg.bufferElementSize(boundaryBufferHandle);
  const sizeBytes = hg.bufferSizeBytes(boundaryBufferHandle);
  
  console.log(`Boundary buffer properties:`);
  console.log(`  Is boundary: ${isBoundary}`);
  console.log(`  Is linear: ${isLinear}`);
  console.log(`  Element size: ${elementSize} bytes`);
  console.log(`  Total size: ${sizeBytes} bytes`);
  
  // Clean up boundary buffer
  hg.bufferCleanup(boundaryBufferHandle);
  console.log('Boundary buffer cleaned up');
} catch (error) {
  console.log(`Boundary buffer allocation failed: ${error}`);
}

// Buffer operations
console.log('\n🔄 Buffer Operations:');
const length = hg.bufferLength(bufferHandle);
console.log(`Buffer length: ${length}`);

// Fill buffer with test data
hg.bufferFill(bufferHandle, 1.5, bufferSize);
console.log(`Filled buffer with value 1.5`);

// Get buffer data
const bufferData = hg.bufferToVec(bufferHandle);
console.log(`Buffer data (first 10 elements): ${bufferData.substring(0, 100)}...`);

// Check buffer properties
const isEmpty = hg.bufferIsEmpty(bufferHandle);
const isLinear = hg.bufferIsLinear(bufferHandle);
const isBoundary = hg.bufferIsBoundary(bufferHandle);
const elementSize = hg.bufferElementSize(bufferHandle);
const sizeBytes = hg.bufferSizeBytes(bufferHandle);
const backendHandle = hg.bufferBackendHandle(bufferHandle);
const topology = hg.bufferTopology(bufferHandle);
const pool = hg.bufferPool(bufferHandle);

console.log('\n📋 Buffer Properties:');
console.log(`  Is empty: ${isEmpty}`);
console.log(`  Is linear: ${isLinear}`);
console.log(`  Is boundary: ${isBoundary}`);
console.log(`  Element size: ${elementSize} bytes`);
console.log(`  Total size: ${sizeBytes} bytes`);
console.log(`  Backend handle: ${backendHandle}`);
console.log(`  Topology: ${topology}`);
console.log(`  Pool: ${pool}`);

// Copy data to buffer
console.log('\n📋 Copying Data to Buffer:');
const testData = JSON.stringify([1.0, 2.0, 3.0, 4.0, 5.0]);
hg.bufferCopyFromSlice(bufferHandle, testData);
console.log(`Copied test data to buffer`);

// Resonance operations
console.log('\n🎵 Resonance Operations:');
for (let i = 0; i < 5; i++) {
  const resonance = hg.executorResonanceAt(executorHandle, i);
  console.log(`Resonance at class ${i}: ${resonance.toFixed(4)}`);
}

// Get resonance snapshot
const resonanceSnapshot = hg.executorResonanceSnapshot(executorHandle);
console.log(`Resonance snapshot: ${resonanceSnapshot}`);

// Mirror operations
console.log('\n🪞 Mirror Operations:');
for (let i = 0; i < 5; i++) {
  const mirror = hg.executorMirror(executorHandle, i);
  console.log(`Mirror of class ${i}: ${mirror}`);
}

// Neighbor operations
console.log('\n👥 Neighbor Operations:');
for (let i = 0; i < 5; i++) {
  const neighbors = hg.executorNeighbors(executorHandle, i);
  console.log(`Neighbors of class ${i}: ${neighbors}`);
}

// Cleanup
console.log('\n🧹 Cleanup:');
hg.bufferCleanup(bufferHandle);
console.log('Buffer cleaned up');

hg.executorCleanup(executorHandle);
console.log('Executor cleaned up');

hg.executorCleanup(customExecutorHandle);
console.log('Custom executor cleaned up');

console.log('\n✅ Executor management example completed successfully!');
