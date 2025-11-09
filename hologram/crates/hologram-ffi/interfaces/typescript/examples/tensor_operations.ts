/**
 * Tensor Operations Example
 * 
 * This example demonstrates comprehensive tensor operations including creation,
 * manipulation, reshaping, broadcasting, and advanced tensor operations.
 */

import * as hg from '../src/index';

console.log('🚀 Hologram FFI - Tensor Operations Example');
console.log('==========================================');

// Create executor
console.log('\n🏗️ Creating Executor:');
const executorHandle = hg.newExecutor();
console.log(`Created executor with handle: ${executorHandle}`);

// Create buffers for tensors
console.log('\n💾 Creating Buffers for Tensors:');
const bufferSize = 1000;
const bufferHandle1 = hg.executorAllocateBuffer(executorHandle, bufferSize);
const bufferHandle2 = hg.executorAllocateBuffer(executorHandle, bufferSize);
console.log(`Created buffers: ${bufferHandle1}, ${bufferHandle2}`);

// Fill buffers with test data
hg.bufferFill(bufferHandle1, 1.0, bufferSize);
hg.bufferFill(bufferHandle2, 2.0, bufferSize);
console.log('Filled buffers with test data');

// Create tensors from buffers
console.log('\n📦 Tensor Creation:');
const shape1 = JSON.stringify([10, 10, 10]); // 3D tensor
const shape2 = JSON.stringify([100, 10]);     // 2D tensor

const tensorHandle1 = hg.tensorFromBuffer(bufferHandle1, shape1);
const tensorHandle2 = hg.tensorFromBuffer(bufferHandle2, shape2);

console.log(`Created tensor 1 with handle: ${tensorHandle1}`);
console.log(`Created tensor 2 with handle: ${tensorHandle2}`);

// Tensor introspection
console.log('\n🔍 Tensor Introspection:');
console.log('\nTensor 1 Properties:');
const shape1Result = hg.tensorShape(tensorHandle1);
const strides1Result = hg.tensorStrides(tensorHandle1);
const offset1 = hg.tensorOffset(tensorHandle1);
const ndim1 = hg.tensorNdim(tensorHandle1);
const numel1 = hg.tensorNumel(tensorHandle1);
const isContiguous1 = hg.tensorIsContiguous(tensorHandle1);

console.log(`  Shape: ${shape1Result}`);
console.log(`  Strides: ${strides1Result}`);
console.log(`  Offset: ${offset1}`);
console.log(`  Dimensions: ${ndim1}`);
console.log(`  Number of elements: ${numel1}`);
console.log(`  Is contiguous: ${isContiguous1}`);

console.log('\nTensor 2 Properties:');
const shape2Result = hg.tensorShape(tensorHandle2);
const strides2Result = hg.tensorStrides(tensorHandle2);
const offset2 = hg.tensorOffset(tensorHandle2);
const ndim2 = hg.tensorNdim(tensorHandle2);
const numel2 = hg.tensorNumel(tensorHandle2);
const isContiguous2 = hg.tensorIsContiguous(tensorHandle2);

console.log(`  Shape: ${shape2Result}`);
console.log(`  Strides: ${strides2Result}`);
console.log(`  Offset: ${offset2}`);
console.log(`  Dimensions: ${ndim2}`);
console.log(`  Number of elements: ${numel2}`);
console.log(`  Is contiguous: ${isContiguous2}`);

// Tensor operations
console.log('\n🔄 Tensor Operations:');

// Reshape tensor
console.log('\n1. Reshaping:');
const newShape = JSON.stringify([50, 20]);
const reshapedTensor = hg.tensorReshape(tensorHandle1, newShape);
console.log(`Reshaped tensor handle: ${reshapedTensor}`);

const reshapedShape = hg.tensorShape(reshapedTensor);
console.log(`New shape: ${reshapedShape}`);

// Transpose tensor
console.log('\n2. Transposing:');
const transposedTensor = hg.tensorTranspose(tensorHandle2);
console.log(`Transposed tensor handle: ${transposedTensor}`);

const transposedShape = hg.tensorShape(transposedTensor);
console.log(`Transposed shape: ${transposedShape}`);

// Permute tensor
console.log('\n3. Permuting:');
const permDims = JSON.stringify([1, 0]); // Swap dimensions
const permutedTensor = hg.tensorPermute(tensorHandle2, permDims);
console.log(`Permuted tensor handle: ${permutedTensor}`);

const permutedShape = hg.tensorShape(permutedTensor);
console.log(`Permuted shape: ${permutedShape}`);

// Create 1D view
console.log('\n4. 1D View:');
const view1dTensor = hg.tensorView1d(tensorHandle1);
console.log(`1D view tensor handle: ${view1dTensor}`);

const view1dShape = hg.tensorShape(view1dTensor);
console.log(`1D view shape: ${view1dShape}`);

// Broadcasting operations
console.log('\n5. Broadcasting:');
const isCompatible = hg.tensorIsBroadcastCompatible(tensorHandle1, tensorHandle2);
console.log(`Tensors are broadcast compatible: ${isCompatible}`);

if (isCompatible) {
  const broadcastShape = hg.tensorBroadcastShape(tensorHandle1, tensorHandle2);
  console.log(`Broadcast shape: ${broadcastShape}`);
}

// Matrix multiplication
console.log('\n6. Matrix Multiplication:');
try {
  const matmulTensor = hg.tensorMatmul(executorHandle, tensorHandle1, tensorHandle2);
  console.log(`Matrix multiplication result tensor handle: ${matmulTensor}`);
  
  const matmulShape = hg.tensorShape(matmulTensor);
  console.log(`Matrix multiplication result shape: ${matmulShape}`);
  
  // Clean up matmul result
  hg.tensorCleanup(matmulTensor);
} catch (error) {
  console.log(`Matrix multiplication failed: ${error}`);
}

// Tensor slicing operations
console.log('\n7. Tensor Slicing:');

// Select operation
const selectedTensor = hg.tensorSelect(tensorHandle1, 0, 5);
console.log(`Selected tensor handle: ${selectedTensor}`);
const selectedShape = hg.tensorShape(selectedTensor);
console.log(`Selected tensor shape: ${selectedShape}`);

// Narrow operation
const narrowedTensor = hg.tensorNarrow(tensorHandle1, 0, 2, 6);
console.log(`Narrowed tensor handle: ${narrowedTensor}`);
const narrowedShape = hg.tensorShape(narrowedTensor);
console.log(`Narrowed tensor shape: ${narrowedShape}`);

// Slice operation
const slicedTensor = hg.tensorSlice(tensorHandle1, 0, 1, 8, 2);
console.log(`Sliced tensor handle: ${slicedTensor}`);
const slicedShape = hg.tensorShape(slicedTensor);
console.log(`Sliced tensor shape: ${slicedShape}`);

// Tensor buffer access
console.log('\n8. Buffer Access:');
const tensorBufferHandle = hg.tensorBuffer(tensorHandle1);
console.log(`Tensor buffer handle: ${tensorBufferHandle}`);

const tensorBufferMutHandle = hg.tensorBufferMut(tensorHandle1);
console.log(`Tensor mutable buffer handle: ${tensorBufferMutHandle}`);

// Create tensor with custom strides
console.log('\n9. Custom Strides:');
const customBufferHandle = hg.executorAllocateBuffer(executorHandle, 200);
hg.bufferFill(customBufferHandle, 3.0, 200);

const customShape = JSON.stringify([10, 20]);
const customStrides = JSON.stringify([20, 1]); // Row-major
const customStridesTensor = hg.tensorFromBufferWithStrides(customBufferHandle, customShape, customStrides);

console.log(`Custom strides tensor handle: ${customStridesTensor}`);
const customShapeResult = hg.tensorShape(customStridesTensor);
const customStridesResult = hg.tensorStrides(customStridesTensor);
console.log(`Custom strides tensor shape: ${customShapeResult}`);
console.log(`Custom strides tensor strides: ${customStridesResult}`);

// Performance test
console.log('\n⚡ Performance Test:');
const perfIterations = 100;
console.log(`Running ${perfIterations} tensor operations...`);

const perfStartTime = Date.now();
let currentTensor = tensorHandle1;

for (let i = 0; i < perfIterations; i++) {
  // Alternate between reshape and transpose
  if (i % 2 === 0) {
    const testShape = JSON.stringify([25, 40]);
    currentTensor = hg.tensorReshape(currentTensor, testShape);
  } else {
    currentTensor = hg.tensorTranspose(currentTensor);
  }
}

const perfEndTime = Date.now();
const perfDuration = perfEndTime - perfStartTime;
const opsPerSecond = (perfIterations / perfDuration) * 1000;

console.log(`Performance results:`);
console.log(`  Duration: ${perfDuration}ms`);
console.log(`  Operations per second: ${opsPerSecond.toFixed(0)}`);
console.log(`  Time per operation: ${(perfDuration / perfIterations).toFixed(3)}ms`);

// Cleanup
console.log('\n🧹 Cleanup:');
hg.tensorCleanup(tensorHandle1);
hg.tensorCleanup(tensorHandle2);
hg.tensorCleanup(reshapedTensor);
hg.tensorCleanup(transposedTensor);
hg.tensorCleanup(permutedTensor);
hg.tensorCleanup(view1dTensor);
hg.tensorCleanup(selectedTensor);
hg.tensorCleanup(narrowedTensor);
hg.tensorCleanup(slicedTensor);
hg.tensorCleanup(customStridesTensor);

hg.bufferCleanup(bufferHandle1);
hg.bufferCleanup(bufferHandle2);
hg.bufferCleanup(customBufferHandle);

hg.executorCleanup(executorHandle);

console.log('All tensors, buffers, and executor cleaned up');

console.log('\n✅ Tensor operations example completed successfully!');
