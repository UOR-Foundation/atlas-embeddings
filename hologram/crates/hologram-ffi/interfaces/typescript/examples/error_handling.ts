/**
 * Error Handling Example
 * 
 * This example demonstrates error handling patterns and graceful failure modes
 * in the hologram-ffi TypeScript bindings.
 */

import * as hg from '../src/index';

console.log('🚀 Hologram FFI - Error Handling Example');
console.log('========================================');

// Test error handling patterns
console.log('\n🛡️ Error Handling Patterns:');

// 1. Invalid handle operations
console.log('\n1. Invalid Handle Operations:');
try {
  const invalidHandle = 999999;
  const phase = hg.executorPhase(invalidHandle);
  console.log(`Unexpected success with invalid handle: ${phase}`);
} catch (error) {
  console.log(`✅ Caught expected error with invalid executor handle: ${error}`);
}

try {
  const invalidBufferHandle = 888888;
  const length = hg.bufferLength(invalidBufferHandle);
  console.log(`Unexpected success with invalid buffer handle: ${length}`);
} catch (error) {
  console.log(`✅ Caught expected error with invalid buffer handle: ${error}`);
}

try {
  const invalidTensorHandle = 777777;
  const shape = hg.tensorShape(invalidTensorHandle);
  console.log(`Unexpected success with invalid tensor handle: ${shape}`);
} catch (error) {
  console.log(`✅ Caught expected error with invalid tensor handle: ${error}`);
}

// 2. Resource cleanup errors
console.log('\n2. Resource Cleanup Errors:');
const executorHandle = hg.newExecutor();
console.log(`Created executor: ${executorHandle}`);

// Clean up executor
hg.executorCleanup(executorHandle);
console.log('Executor cleaned up');

// Try to use cleaned up executor
try {
  const phase = hg.executorPhase(executorHandle);
  console.log(`Unexpected success with cleaned up executor: ${phase}`);
} catch (error) {
  console.log(`✅ Caught expected error with cleaned up executor: ${error}`);
}

// 3. Buffer allocation errors
console.log('\n3. Buffer Allocation Errors:');
const newExecutorHandle = hg.newExecutor();
console.log(`Created new executor: ${newExecutorHandle}`);

try {
  // Try to allocate extremely large buffer
  const hugeBufferHandle = hg.executorAllocateBuffer(newExecutorHandle, 0xFFFFFFFF);
  console.log(`Unexpected success with huge buffer: ${hugeBufferHandle}`);
} catch (error) {
  console.log(`✅ Caught expected error with huge buffer allocation: ${error}`);
}

try {
  // Try to allocate buffer with invalid executor
  const invalidExecutorHandle = 123456;
  const bufferHandle = hg.executorAllocateBuffer(invalidExecutorHandle, 100);
  console.log(`Unexpected success with invalid executor: ${bufferHandle}`);
} catch (error) {
  console.log(`✅ Caught expected error with invalid executor: ${error}`);
}

// 4. Boundary buffer allocation errors
console.log('\n4. Boundary Buffer Allocation Errors:');
try {
  // Try to allocate boundary buffer with invalid parameters
  const boundaryHandle = hg.executorAllocateBoundaryBuffer(newExecutorHandle, 999, 0, 0);
  console.log(`Unexpected success with invalid boundary buffer: ${boundaryHandle}`);
} catch (error) {
  console.log(`✅ Caught expected error with invalid boundary buffer: ${error}`);
}

// 5. Tensor operation errors
console.log('\n5. Tensor Operation Errors:');
const bufferHandle = hg.executorAllocateBuffer(newExecutorHandle, 100);
console.log(`Created buffer: ${bufferHandle}`);

try {
  // Try to create tensor with invalid shape
  const invalidShape = JSON.stringify([-1, 10]); // Negative dimension
  const tensorHandle = hg.tensorFromBuffer(bufferHandle, invalidShape);
  console.log(`Unexpected success with invalid tensor shape: ${tensorHandle}`);
} catch (error) {
  console.log(`✅ Caught expected error with invalid tensor shape: ${error}`);
}

try {
  // Try to create tensor with mismatched shape and buffer size
  const mismatchedShape = JSON.stringify([1000, 1000]); // Too large for buffer
  const tensorHandle = hg.tensorFromBuffer(bufferHandle, mismatchedShape);
  console.log(`Unexpected success with mismatched tensor shape: ${tensorHandle}`);
} catch (error) {
  console.log(`✅ Caught expected error with mismatched tensor shape: ${error}`);
}

// 6. Matrix multiplication errors
console.log('\n6. Matrix Multiplication Errors:');
const buffer1Handle = hg.executorAllocateBuffer(newExecutorHandle, 100);
const buffer2Handle = hg.executorAllocateBuffer(newExecutorHandle, 200);
hg.bufferFill(buffer1Handle, 1.0, 100);
hg.bufferFill(buffer2Handle, 2.0, 200);

const shape1 = JSON.stringify([10, 10]);
const shape2 = JSON.stringify([20, 10]);
const tensor1Handle = hg.tensorFromBuffer(buffer1Handle, shape1);
const tensor2Handle = hg.tensorFromBuffer(buffer2Handle, shape2);

try {
  // Try matrix multiplication with incompatible shapes
  const matmulHandle = hg.tensorMatmul(newExecutorHandle, tensor1Handle, tensor2Handle);
  console.log(`Unexpected success with incompatible matrix shapes: ${matmulHandle}`);
} catch (error) {
  console.log(`✅ Caught expected error with incompatible matrix shapes: ${error}`);
}

// 7. Broadcasting errors
console.log('\n7. Broadcasting Errors:');
const incompatibleShape1 = JSON.stringify([5, 5]);
const incompatibleShape2 = JSON.stringify([3, 3]);
const tensor3Handle = hg.tensorFromBuffer(buffer1Handle, incompatibleShape1);
const tensor4Handle = hg.tensorFromBuffer(buffer2Handle, incompatibleShape2);

const isCompatible = hg.tensorIsBroadcastCompatible(tensor3Handle, tensor4Handle);
console.log(`Broadcast compatibility check: ${isCompatible}`);

if (!isCompatible) {
  try {
    const broadcastShape = hg.tensorBroadcastShape(tensor3Handle, tensor4Handle);
    console.log(`Unexpected success with incompatible broadcast: ${broadcastShape}`);
  } catch (error) {
    console.log(`✅ Caught expected error with incompatible broadcast: ${error}`);
  }
}

// 8. Slice operation errors
console.log('\n8. Slice Operation Errors:');
try {
  // Try to slice with invalid parameters
  const slicedTensor = hg.tensorSlice(tensor1Handle, 0, 10, 5, 1); // start > end
  console.log(`Unexpected success with invalid slice parameters: ${slicedTensor}`);
} catch (error) {
  console.log(`✅ Caught expected error with invalid slice parameters: ${error}`);
}

try {
  // Try to slice with invalid dimension
  const slicedTensor = hg.tensorSlice(tensor1Handle, 10, 0, 5, 1); // invalid dimension
  console.log(`Unexpected success with invalid slice dimension: ${slicedTensor}`);
} catch (error) {
  console.log(`✅ Caught expected error with invalid slice dimension: ${error}`);
}

// 9. JSON parsing errors
console.log('\n9. JSON Parsing Errors:');
try {
  // Try to copy invalid JSON data
  const invalidJson = '{"invalid": json}';
  hg.bufferCopyFromSlice(bufferHandle, invalidJson);
  console.log('Unexpected success with invalid JSON');
} catch (error) {
  console.log(`✅ Caught expected error with invalid JSON: ${error}`);
}

// 10. Resource exhaustion simulation
console.log('\n10. Resource Exhaustion Simulation:');
const handles: number[] = [];
let handleCount = 0;

try {
  // Try to create many executors to test resource limits
  for (let i = 0; i < 1000; i++) {
    const handle = hg.newExecutor();
    handles.push(handle);
    handleCount++;
  }
  console.log(`Created ${handleCount} executors successfully`);
} catch (error) {
  console.log(`✅ Caught expected error after creating ${handleCount} executors: ${error}`);
}

// Clean up all created handles
console.log('\n🧹 Cleanup:');
for (const handle of handles) {
  try {
    hg.executorCleanup(handle);
  } catch (error) {
    console.log(`Error cleaning up executor ${handle}: ${error}`);
  }
}

// Clean up remaining resources
try {
  hg.tensorCleanup(tensor1Handle);
  hg.tensorCleanup(tensor2Handle);
  hg.tensorCleanup(tensor3Handle);
  hg.tensorCleanup(tensor4Handle);
  hg.bufferCleanup(bufferHandle);
  hg.bufferCleanup(buffer1Handle);
  hg.bufferCleanup(buffer2Handle);
  hg.executorCleanup(newExecutorHandle);
  console.log('All resources cleaned up successfully');
} catch (error) {
  console.log(`Error during cleanup: ${error}`);
}

// 11. Graceful degradation test
console.log('\n11. Graceful Degradation Test:');
console.log('Testing mock library fallback...');

// The mock library should handle all operations gracefully
const mockVersion = hg.getVersion();
console.log(`Mock version: ${mockVersion}`);

const mockPhase = hg.atlasPhase();
console.log(`Mock Atlas phase: ${mockPhase}`);

console.log('\n✅ Error handling example completed successfully!');
console.log('All error conditions were handled gracefully.');
