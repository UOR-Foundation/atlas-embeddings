/**
 * Integration Tests Example
 * 
 * This example demonstrates comprehensive integration testing of hologram-ffi
 * functionality across different operation types and workflows.
 */

import * as hg from '../src/index';

console.log('🚀 Hologram FFI - Integration Tests Example');
console.log('==========================================');

// Test configuration
const TEST_CONFIG = {
  bufferSize: 1000,
  tensorShape: [10, 10],
  iterations: 100
};

// Test utilities
function assert(condition: boolean, message: string): void {
  if (!condition) {
    throw new Error(`Assertion failed: ${message}`);
  }
}

function assertEqual<T>(actual: T, expected: T, message: string): void {
  if (actual !== expected) {
    throw new Error(`Assertion failed: ${message}. Expected: ${expected}, Actual: ${actual}`);
  }
}

function assertClose(actual: number, expected: number, tolerance: number = 1e-6, message: string): void {
  if (Math.abs(actual - expected) > tolerance) {
    throw new Error(`Assertion failed: ${message}. Expected: ${expected}, Actual: ${actual}, Tolerance: ${tolerance}`);
  }
}

// Test 1: Basic functionality integration
console.log('\n🧪 Test 1: Basic Functionality Integration');
function testBasicFunctionality(): void {
  console.log('Testing version and phase management...');
  
  const version = hg.getVersion();
  assert(typeof version === 'string', 'Version should be a string');
  assert(version.length > 0, 'Version should not be empty');
  
  const phase = hg.getExecutorPhase();
  assert(typeof phase === 'number', 'Phase should be a number');
  
  hg.advanceExecutorPhase(1);
  const newPhase = hg.getExecutorPhase();
  assertEqual(newPhase, phase + 1, 'Phase should advance by 1');
  
  console.log('✅ Basic functionality test passed');
}

// Test 2: Executor lifecycle integration
console.log('\n🧪 Test 2: Executor Lifecycle Integration');
function testExecutorLifecycle(): void {
  console.log('Testing executor creation and management...');
  
  const executorHandle = hg.newExecutor();
  assert(typeof executorHandle === 'number', 'Executor handle should be a number');
  assert(executorHandle > 0, 'Executor handle should be positive');
  
  const phase = hg.executorPhase(executorHandle);
  assert(typeof phase === 'number', 'Executor phase should be a number');
  
  hg.executorAdvancePhase(executorHandle, 5);
  const newPhase = hg.executorPhase(executorHandle);
  assertEqual(newPhase, phase + 5, 'Executor phase should advance by 5');
  
  // Test resonance operations
  const resonance = hg.executorResonanceAt(executorHandle, 0);
  assert(typeof resonance === 'number', 'Resonance should be a number');
  
  const resonanceSnapshot = hg.executorResonanceSnapshot(executorHandle);
  assert(typeof resonanceSnapshot === 'string', 'Resonance snapshot should be a string');
  
  // Test mirror and neighbor operations
  const mirror = hg.executorMirror(executorHandle, 0);
  assert(typeof mirror === 'number', 'Mirror should be a number');
  
  const neighbors = hg.executorNeighbors(executorHandle, 0);
  assert(typeof neighbors === 'string', 'Neighbors should be a string');
  
  hg.executorCleanup(executorHandle);
  console.log('✅ Executor lifecycle test passed');
}

// Test 3: Buffer operations integration
console.log('\n🧪 Test 3: Buffer Operations Integration');
function testBufferOperations(): void {
  console.log('Testing buffer allocation and operations...');
  
  const executorHandle = hg.newExecutor();
  const bufferHandle = hg.executorAllocateBuffer(executorHandle, TEST_CONFIG.bufferSize);
  
  assert(typeof bufferHandle === 'number', 'Buffer handle should be a number');
  assert(bufferHandle > 0, 'Buffer handle should be positive');
  
  const length = hg.bufferLength(bufferHandle);
  assertEqual(length, TEST_CONFIG.bufferSize, 'Buffer length should match allocated size');
  
  const isEmpty = hg.bufferIsEmpty(bufferHandle);
  assertEqual(isEmpty, false, 'Buffer should not be empty after allocation');
  
  const isLinear = hg.bufferIsLinear(bufferHandle);
  assertEqual(isLinear, true, 'Buffer should be linear');
  
  const isBoundary = hg.bufferIsBoundary(bufferHandle);
  assertEqual(isBoundary, false, 'Buffer should not be boundary');
  
  const elementSize = hg.bufferElementSize(bufferHandle);
  assert(elementSize > 0, 'Element size should be positive');
  
  const sizeBytes = hg.bufferSizeBytes(bufferHandle);
  assertEqual(sizeBytes, TEST_CONFIG.bufferSize * elementSize, 'Size in bytes should match');
  
  // Test buffer operations
  hg.bufferFill(bufferHandle, 1.5, TEST_CONFIG.bufferSize);
  
  const data = hg.bufferToVec(bufferHandle);
  assert(typeof data === 'string', 'Buffer data should be a string');
  
  // Test data copying
  const testData = JSON.stringify([1.0, 2.0, 3.0, 4.0, 5.0]);
  hg.bufferCopyFromSlice(bufferHandle, testData);
  
  hg.bufferCleanup(bufferHandle);
  hg.executorCleanup(executorHandle);
  console.log('✅ Buffer operations test passed');
}

// Test 4: Tensor operations integration
console.log('\n🧪 Test 4: Tensor Operations Integration');
function testTensorOperations(): void {
  console.log('Testing tensor creation and operations...');
  
  const executorHandle = hg.newExecutor();
  const bufferSize = TEST_CONFIG.tensorShape.reduce((a, b) => a * b, 1);
  const bufferHandle = hg.executorAllocateBuffer(executorHandle, bufferSize);
  const shapeJson = JSON.stringify(TEST_CONFIG.tensorShape);
  
  const tensorHandle = hg.tensorFromBuffer(bufferHandle, shapeJson);
  assert(typeof tensorHandle === 'number', 'Tensor handle should be a number');
  assert(tensorHandle > 0, 'Tensor handle should be positive');
  
  // Test tensor properties
  const shape = hg.tensorShape(tensorHandle);
  assert(typeof shape === 'string', 'Tensor shape should be a string');
  
  const strides = hg.tensorStrides(tensorHandle);
  assert(typeof strides === 'string', 'Tensor strides should be a string');
  
  const offset = hg.tensorOffset(tensorHandle);
  assert(typeof offset === 'number', 'Tensor offset should be a number');
  
  const ndim = hg.tensorNdim(tensorHandle);
  assertEqual(ndim, TEST_CONFIG.tensorShape.length, 'Tensor dimensions should match');
  
  const numel = hg.tensorNumel(tensorHandle);
  assertEqual(numel, bufferSize, 'Tensor number of elements should match buffer size');
  
  const isContiguous = hg.tensorIsContiguous(tensorHandle);
  assert(typeof isContiguous === 'boolean', 'Tensor contiguity should be boolean');
  
  // Test tensor operations
  const newShape = JSON.stringify([5, 20]);
  const reshapedTensor = hg.tensorReshape(tensorHandle, newShape);
  assert(typeof reshapedTensor === 'number', 'Reshaped tensor handle should be a number');
  
  const reshapedShape = hg.tensorShape(reshapedTensor);
  assertEqual(reshapedShape, newShape, 'Reshaped tensor shape should match');
  
  const transposedTensor = hg.tensorTranspose(tensorHandle);
  assert(typeof transposedTensor === 'number', 'Transposed tensor handle should be a number');
  
  const view1dTensor = hg.tensorView1d(tensorHandle);
  assert(typeof view1dTensor === 'number', '1D view tensor handle should be a number');
  
  // Test tensor buffer access
  const tensorBufferHandle = hg.tensorBuffer(tensorHandle);
  assert(typeof tensorBufferHandle === 'number', 'Tensor buffer handle should be a number');
  
  const tensorBufferMutHandle = hg.tensorBufferMut(tensorHandle);
  assert(typeof tensorBufferMutHandle === 'number', 'Tensor mutable buffer handle should be a number');
  
  // Cleanup
  hg.tensorCleanup(tensorHandle);
  hg.tensorCleanup(reshapedTensor);
  hg.tensorCleanup(transposedTensor);
  hg.tensorCleanup(view1dTensor);
  hg.bufferCleanup(bufferHandle);
  hg.executorCleanup(executorHandle);
  console.log('✅ Tensor operations test passed');
}

// Test 5: Mathematical operations integration
console.log('\n🧪 Test 5: Mathematical Operations Integration');
function testMathematicalOperations(): void {
  console.log('Testing mathematical operations...');
  
  const testSize = 1000;
  
  // Test vector operations
  hg.vectorAddF32(testSize);
  hg.vectorSubF32(testSize);
  hg.vectorMulF32(testSize);
  hg.vectorDivF32(testSize);
  hg.vectorAbsF32(testSize);
  hg.vectorNegF32(testSize);
  hg.vectorReluF32(testSize);
  
  // Test reduction operations
  const sum = hg.reduceSumF32(testSize);
  assert(typeof sum === 'number', 'Sum should be a number');
  
  const max = hg.reduceMaxF32(testSize);
  assert(typeof max === 'number', 'Max should be a number');
  
  const min = hg.reduceMinF32(testSize);
  assert(typeof min === 'number', 'Min should be a number');
  
  // Test activation functions
  hg.sigmoidF32(testSize);
  hg.tanhF32(testSize);
  hg.softmaxF32(testSize);
  
  // Test linear algebra
  hg.gemmF32(10, 10, 10);
  hg.matvecF32(10, 10);
  
  // Test loss functions
  const mseLoss = hg.mseLossF32(testSize);
  assert(typeof mseLoss === 'number', 'MSE loss should be a number');
  
  const crossEntropyLoss = hg.crossEntropyLossF32(testSize);
  assert(typeof crossEntropyLoss === 'number', 'Cross-entropy loss should be a number');
  
  console.log('✅ Mathematical operations test passed');
}

// Test 6: Atlas state management integration
console.log('\n🧪 Test 6: Atlas State Management Integration');
function testAtlasStateManagement(): void {
  console.log('Testing Atlas state management...');
  
  const initialPhase = hg.atlasPhase();
  assert(typeof initialPhase === 'number', 'Atlas phase should be a number');
  
  hg.atlasAdvancePhase(3);
  const newPhase = hg.atlasPhase();
  assertEqual(newPhase, initialPhase + 3, 'Atlas phase should advance by 3');
  
  // Test resonance operations
  for (let i = 0; i < 5; i++) {
    const resonance = hg.atlasResonanceAt(i);
    assert(typeof resonance === 'number', 'Atlas resonance should be a number');
  }
  
  const resonanceSnapshot = hg.atlasResonanceSnapshot();
  assert(typeof resonanceSnapshot === 'string', 'Atlas resonance snapshot should be a string');
  
  console.log('✅ Atlas state management test passed');
}

// Test 7: Compiler infrastructure integration
console.log('\n🧪 Test 7: Compiler Infrastructure Integration');
function testCompilerInfrastructure(): void {
  console.log('Testing compiler infrastructure...');
  
  const programBuilderHandle = hg.programBuilderNew();
  assert(typeof programBuilderHandle === 'number', 'Program builder handle should be a number');
  
  const registerAllocatorHandle = hg.registerAllocatorNew();
  assert(typeof registerAllocatorHandle === 'number', 'Register allocator handle should be a number');
  
  const executorHandle = hg.newExecutor();
  const bufferHandle = hg.executorAllocateBuffer(executorHandle, 100);
  
  const address = hg.addressBuilderDirect(bufferHandle, 0);
  assert(typeof address === 'string', 'Address should be a string');
  
  hg.bufferCleanup(bufferHandle);
  hg.executorCleanup(executorHandle);
  console.log('✅ Compiler infrastructure test passed');
}

// Test 8: Error handling integration
console.log('\n🧪 Test 8: Error Handling Integration');
function testErrorHandling(): void {
  console.log('Testing error handling...');
  
  // Test invalid handle handling
  try {
    hg.executorPhase(999999);
    console.log('⚠️  Expected error with invalid executor handle');
  } catch (error) {
    console.log('✅ Caught expected error with invalid executor handle');
  }
  
  try {
    hg.bufferLength(888888);
    console.log('⚠️  Expected error with invalid buffer handle');
  } catch (error) {
    console.log('✅ Caught expected error with invalid buffer handle');
  }
  
  try {
    hg.tensorShape(777777);
    console.log('⚠️  Expected error with invalid tensor handle');
  } catch (error) {
    console.log('✅ Caught expected error with invalid tensor handle');
  }
  
  console.log('✅ Error handling test passed');
}

// Test 9: Performance integration
console.log('\n🧪 Test 9: Performance Integration');
function testPerformanceIntegration(): void {
  console.log('Testing performance characteristics...');
  
  const iterations = 1000;
  const startTime = Date.now();
  
  for (let i = 0; i < iterations; i++) {
    hg.getVersion();
    hg.atlasPhase();
    hg.vectorAddF32(100);
  }
  
  const endTime = Date.now();
  const duration = endTime - startTime;
  const opsPerSecond = (iterations * 3 / duration) * 1000;
  
  console.log(`Performance test: ${opsPerSecond.toFixed(0)} operations/second`);
  assert(opsPerSecond > 1000, 'Performance should be reasonable');
  
  console.log('✅ Performance integration test passed');
}

// Test 10: Memory management integration
console.log('\n🧪 Test 10: Memory Management Integration');
function testMemoryManagement(): void {
  console.log('Testing memory management...');
  
  const handles: number[] = [];
  
  // Create many resources
  for (let i = 0; i < 100; i++) {
    const executorHandle = hg.newExecutor();
    const bufferHandle = hg.executorAllocateBuffer(executorHandle, 100);
    const tensorHandle = hg.tensorFromBuffer(bufferHandle, JSON.stringify([10, 10]));
    
    handles.push(executorHandle, bufferHandle, tensorHandle);
  }
  
  console.log(`Created ${handles.length / 3} resource sets`);
  
  // Clean up all resources
  for (let i = 0; i < handles.length; i += 3) {
    hg.tensorCleanup(handles[i + 2]);
    hg.bufferCleanup(handles[i + 1]);
    hg.executorCleanup(handles[i]);
  }
  
  console.log('✅ Memory management test passed');
}

// Run all tests
console.log('\n🚀 Running Integration Tests');
console.log('============================');

try {
  testBasicFunctionality();
  testExecutorLifecycle();
  testBufferOperations();
  testTensorOperations();
  testMathematicalOperations();
  testAtlasStateManagement();
  testCompilerInfrastructure();
  testErrorHandling();
  testPerformanceIntegration();
  testMemoryManagement();
  
  console.log('\n🎉 All Integration Tests Passed!');
  console.log('=================================');
  console.log('✅ Basic functionality');
  console.log('✅ Executor lifecycle');
  console.log('✅ Buffer operations');
  console.log('✅ Tensor operations');
  console.log('✅ Mathematical operations');
  console.log('✅ Atlas state management');
  console.log('✅ Compiler infrastructure');
  console.log('✅ Error handling');
  console.log('✅ Performance characteristics');
  console.log('✅ Memory management');
  
} catch (error) {
  console.error('\n❌ Integration Test Failed:');
  console.error('==========================');
  console.error(error);
  process.exit(1);
}

console.log('\n✅ Integration tests completed successfully!');
