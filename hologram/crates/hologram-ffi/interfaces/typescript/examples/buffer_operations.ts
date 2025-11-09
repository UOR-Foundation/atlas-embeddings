/**
 * Buffer Operations Example
 * 
 * This example demonstrates comprehensive buffer operations including allocation,
 * data manipulation, copying, and memory management.
 */

import * as hg from '../src/index';

console.log('🚀 Hologram FFI - Buffer Operations Example');
console.log('===========================================');

// Create executor
console.log('\n🏗️ Creating Executor:');
const executorHandle = hg.newExecutor();
console.log(`Created executor with handle: ${executorHandle}`);

// Allocate multiple buffers
console.log('\n💾 Buffer Allocation:');
const bufferSizes = [100, 500, 1000, 2000];
const bufferHandles: number[] = [];

for (let i = 0; i < bufferSizes.length; i++) {
  const size = bufferSizes[i];
  const handle = hg.executorAllocateBuffer(executorHandle, size);
  bufferHandles.push(handle);
  console.log(`Allocated buffer ${i + 1}: handle=${handle}, size=${size}`);
}

// Buffer properties and introspection
console.log('\n📋 Buffer Properties:');
for (let i = 0; i < bufferHandles.length; i++) {
  const handle = bufferHandles[i];
  const length = hg.bufferLength(handle);
  const isEmpty = hg.bufferIsEmpty(handle);
  const isLinear = hg.bufferIsLinear(handle);
  const isBoundary = hg.bufferIsBoundary(handle);
  const elementSize = hg.bufferElementSize(handle);
  const sizeBytes = hg.bufferSizeBytes(handle);
  const backendHandle = hg.bufferBackendHandle(handle);
  const topology = hg.bufferTopology(handle);
  const pool = hg.bufferPool(handle);

  console.log(`\nBuffer ${i + 1} (handle: ${handle}):`);
  console.log(`  Length: ${length}`);
  console.log(`  Is empty: ${isEmpty}`);
  console.log(`  Is linear: ${isLinear}`);
  console.log(`  Is boundary: ${isBoundary}`);
  console.log(`  Element size: ${elementSize} bytes`);
  console.log(`  Total size: ${sizeBytes} bytes`);
  console.log(`  Backend handle: ${backendHandle}`);
  console.log(`  Topology: ${topology}`);
  console.log(`  Pool: ${pool}`);
}

// Fill buffers with different values
console.log('\n🎨 Buffer Filling:');
const fillValues = [0.0, 1.0, 2.5, -1.0];
for (let i = 0; i < bufferHandles.length; i++) {
  const handle = bufferHandles[i];
  const value = fillValues[i % fillValues.length];
  const size = bufferSizes[i];
  
  hg.bufferFill(handle, value, size);
  console.log(`Filled buffer ${i + 1} with value ${value}`);
}

// Copy data between buffers
console.log('\n📋 Buffer Copying:');
if (bufferHandles.length >= 2) {
  const srcHandle = bufferHandles[0];
  const dstHandle = bufferHandles[1];
  const copySize = Math.min(bufferSizes[0], bufferSizes[1]);
  
  console.log(`Copying ${copySize} elements from buffer 1 to buffer 2`);
  hg.bufferCopy(srcHandle, dstHandle, copySize);
  console.log('Copy operation completed');
}

// Copy data from JavaScript arrays
console.log('\n📊 Copying from JavaScript Arrays:');
const testData = [
  [1.0, 2.0, 3.0, 4.0, 5.0],
  [0.5, 1.5, 2.5, 3.5, 4.5],
  [-1.0, 0.0, 1.0, 2.0, 3.0],
  [10.0, 20.0, 30.0, 40.0, 50.0]
];

for (let i = 0; i < Math.min(bufferHandles.length, testData.length); i++) {
  const handle = bufferHandles[i];
  const data = testData[i];
  const dataJson = JSON.stringify(data);
  
  hg.bufferCopyFromSlice(handle, dataJson);
  console.log(`Copied data to buffer ${i + 1}: [${data.join(', ')}]`);
}

// Read buffer data
console.log('\n📖 Reading Buffer Data:');
for (let i = 0; i < bufferHandles.length; i++) {
  const handle = bufferHandles[i];
  const data = hg.bufferToVec(handle);
  
  // Parse JSON and show first few elements
  try {
    const parsedData = JSON.parse(data);
    const preview = parsedData.slice(0, 5).join(', ');
    const more = parsedData.length > 5 ? '...' : '';
    console.log(`Buffer ${i + 1} data: [${preview}${more}] (${parsedData.length} elements)`);
  } catch (error) {
    console.log(`Buffer ${i + 1} data: ${data.substring(0, 100)}...`);
  }
}

// Memory usage analysis
console.log('\n💾 Memory Usage Analysis:');
let totalBytes = 0;
for (let i = 0; i < bufferHandles.length; i++) {
  const handle = bufferHandles[i];
  const sizeBytes = hg.bufferSizeBytes(handle);
  totalBytes += sizeBytes;
  console.log(`Buffer ${i + 1}: ${sizeBytes} bytes`);
}
console.log(`Total memory usage: ${totalBytes} bytes (${(totalBytes / 1024).toFixed(2)} KB)`);

// Buffer operations with different data types
console.log('\n🔢 Different Data Operations:');
const operationsBuffer = bufferHandles[0];
const operationSize = bufferSizes[0];

// Test different fill values
const testValues = [0.0, 1.0, -1.0, 3.14159, 2.71828];
for (const value of testValues) {
  hg.bufferFill(operationsBuffer, value, operationSize);
  console.log(`Filled buffer with value: ${value}`);
  
  // Read back a sample to verify
  const data = hg.bufferToVec(operationsBuffer);
  try {
    const parsedData = JSON.parse(data);
    const sampleValue = parsedData[0];
    console.log(`  Sample value read back: ${sampleValue}`);
  } catch (error) {
    console.log(`  Data read back: ${data.substring(0, 50)}...`);
  }
}

// Performance test
console.log('\n⚡ Performance Test:');
const perfBuffer = bufferHandles[0];
const perfSize = bufferSizes[0];
const iterations = 1000;

console.log(`Running ${iterations} fill operations...`);
const startTime = Date.now();

for (let i = 0; i < iterations; i++) {
  hg.bufferFill(perfBuffer, Math.random(), perfSize);
}

const endTime = Date.now();
const duration = endTime - startTime;
const opsPerSecond = (iterations / duration) * 1000;

console.log(`Performance results:`);
console.log(`  Duration: ${duration}ms`);
console.log(`  Operations per second: ${opsPerSecond.toFixed(0)}`);
console.log(`  Time per operation: ${(duration / iterations).toFixed(3)}ms`);

// Cleanup
console.log('\n🧹 Cleanup:');
for (let i = 0; i < bufferHandles.length; i++) {
  hg.bufferCleanup(bufferHandles[i]);
  console.log(`Buffer ${i + 1} cleaned up`);
}

hg.executorCleanup(executorHandle);
console.log('Executor cleaned up');

console.log('\n✅ Buffer operations example completed successfully!');
