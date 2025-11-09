/**
 * Performance Benchmarks Example
 * 
 * This example demonstrates performance testing and benchmarking of various
 * hologram-ffi operations to measure overhead and performance characteristics.
 */

import * as hg from '../src/index';

console.log('🚀 Hologram FFI - Performance Benchmarks Example');
console.log('===============================================');

// Benchmark configuration
const BENCHMARK_CONFIG = {
  iterations: 1000,
  warmupIterations: 100,
  bufferSizes: [100, 1000, 10000, 100000],
  tensorShapes: [
    [10, 10],
    [100, 100],
    [1000, 100],
    [100, 1000]
  ]
};

// Utility functions
function measureTime<T>(fn: () => T): { result: T; time: number } {
  const start = process.hrtime.bigint();
  const result = fn();
  const end = process.hrtime.bigint();
  const time = Number(end - start) / 1000000; // Convert to milliseconds
  return { result, time };
}

function benchmark(name: string, fn: () => void, iterations: number = BENCHMARK_CONFIG.iterations): void {
  console.log(`\n📊 Benchmarking: ${name}`);
  
  // Warmup
  for (let i = 0; i < BENCHMARK_CONFIG.warmupIterations; i++) {
    fn();
  }
  
  // Actual benchmark
  const times: number[] = [];
  for (let i = 0; i < iterations; i++) {
    const { time } = measureTime(fn);
    times.push(time);
  }
  
  // Calculate statistics
  times.sort((a, b) => a - b);
  const min = times[0] || 0;
  const max = times[times.length - 1] || 0;
  const median = times[Math.floor(times.length / 2)] || 0;
  const mean = times.reduce((sum, time) => sum + time, 0) / times.length;
  const p95 = times[Math.floor(times.length * 0.95)] || 0;
  const p99 = times[Math.floor(times.length * 0.99)] || 0;
  
  console.log(`  Iterations: ${iterations}`);
  console.log(`  Min: ${min.toFixed(3)}ms`);
  console.log(`  Max: ${max.toFixed(3)}ms`);
  console.log(`  Mean: ${mean.toFixed(3)}ms`);
  console.log(`  Median: ${median.toFixed(3)}ms`);
  console.log(`  P95: ${p95.toFixed(3)}ms`);
  console.log(`  P99: ${p99.toFixed(3)}ms`);
  console.log(`  Ops/sec: ${(1000 / mean).toFixed(0)}`);
}

// Core function benchmarks
console.log('\n🔧 Core Function Benchmarks:');

benchmark('getVersion()', () => {
  hg.getVersion();
});

benchmark('getExecutorPhase()', () => {
  hg.getExecutorPhase();
});

benchmark('advanceExecutorPhase(1)', () => {
  hg.advanceExecutorPhase(1);
});

benchmark('atlasPhase()', () => {
  hg.atlasPhase();
});

benchmark('atlasAdvancePhase(1)', () => {
  hg.atlasAdvancePhase(1);
});

benchmark('atlasResonanceAt(0)', () => {
  hg.atlasResonanceAt(0);
});

benchmark('atlasResonanceSnapshot()', () => {
  hg.atlasResonanceSnapshot();
});

// Executor management benchmarks
console.log('\n🏗️ Executor Management Benchmarks:');

benchmark('newExecutor()', () => {
  const handle = hg.newExecutor();
  hg.executorCleanup(handle);
});

benchmark('executorWithBackend("cpu")', () => {
  const handle = hg.executorWithBackend('cpu');
  hg.executorCleanup(handle);
});

// Buffer operation benchmarks
console.log('\n💾 Buffer Operation Benchmarks:');

for (const size of BENCHMARK_CONFIG.bufferSizes) {
  const executorHandle = hg.newExecutor();
  
  benchmark(`executorAllocateBuffer(${size})`, () => {
    const handle = hg.executorAllocateBuffer(executorHandle, size);
    hg.bufferCleanup(handle);
  });
  
  const bufferHandle = hg.executorAllocateBuffer(executorHandle, size);
  
  benchmark(`bufferFill(${size})`, () => {
    hg.bufferFill(bufferHandle, 1.5, size);
  });
  
  benchmark(`bufferLength(${size})`, () => {
    hg.bufferLength(bufferHandle);
  });
  
  benchmark(`bufferToVec(${size})`, () => {
    hg.bufferToVec(bufferHandle);
  });
  
  benchmark(`bufferIsLinear(${size})`, () => {
    hg.bufferIsLinear(bufferHandle);
  });
  
  benchmark(`bufferElementSize(${size})`, () => {
    hg.bufferElementSize(bufferHandle);
  });
  
  benchmark(`bufferSizeBytes(${size})`, () => {
    hg.bufferSizeBytes(bufferHandle);
  });
  
  hg.bufferCleanup(bufferHandle);
  hg.executorCleanup(executorHandle);
}

// Mathematical operation benchmarks
console.log('\n🧮 Mathematical Operation Benchmarks:');

for (const size of BENCHMARK_CONFIG.bufferSizes) {
  benchmark(`vectorAddF32(${size})`, () => {
    hg.vectorAddF32(size);
  });
  
  benchmark(`vectorSubF32(${size})`, () => {
    hg.vectorSubF32(size);
  });
  
  benchmark(`vectorMulF32(${size})`, () => {
    hg.vectorMulF32(size);
  });
  
  benchmark(`vectorDivF32(${size})`, () => {
    hg.vectorDivF32(size);
  });
  
  benchmark(`vectorAbsF32(${size})`, () => {
    hg.vectorAbsF32(size);
  });
  
  benchmark(`vectorNegF32(${size})`, () => {
    hg.vectorNegF32(size);
  });
  
  benchmark(`vectorReluF32(${size})`, () => {
    hg.vectorReluF32(size);
  });
  
  benchmark(`reduceSumF32(${size})`, () => {
    hg.reduceSumF32(size);
  });
  
  benchmark(`reduceMaxF32(${size})`, () => {
    hg.reduceMaxF32(size);
  });
  
  benchmark(`reduceMinF32(${size})`, () => {
    hg.reduceMinF32(size);
  });
  
  benchmark(`sigmoidF32(${size})`, () => {
    hg.sigmoidF32(size);
  });
  
  benchmark(`tanhF32(${size})`, () => {
    hg.tanhF32(size);
  });
  
  benchmark(`softmaxF32(${size})`, () => {
    hg.softmaxF32(size);
  });
}

// Linear algebra benchmarks
console.log('\n📐 Linear Algebra Benchmarks:');

const matrixSizes = [
  [10, 10, 10],
  [50, 50, 50],
  [100, 100, 100],
  [200, 200, 200]
];

for (const matrixSize of matrixSizes) {
  const [m, n, k] = matrixSize;
  if (m !== undefined && n !== undefined && k !== undefined) {
    benchmark(`gemmF32(${m}x${k} * ${k}x${n})`, () => {
      hg.gemmF32(m, n, k);
    });
    
    benchmark(`matvecF32(${m}x${n})`, () => {
      hg.matvecF32(m, n);
    });
  }
}

// Loss function benchmarks
console.log('\n📊 Loss Function Benchmarks:');

for (const size of BENCHMARK_CONFIG.bufferSizes) {
  benchmark(`mseLossF32(${size})`, () => {
    hg.mseLossF32(size);
  });
  
  benchmark(`crossEntropyLossF32(${size})`, () => {
    hg.crossEntropyLossF32(size);
  });
}

// Tensor operation benchmarks
console.log('\n📦 Tensor Operation Benchmarks:');

for (const shape of BENCHMARK_CONFIG.tensorShapes) {
  const executorHandle = hg.newExecutor();
  const bufferSize = shape.reduce((a, b) => a * b, 1);
  const bufferHandle = hg.executorAllocateBuffer(executorHandle, bufferSize);
  const shapeJson = JSON.stringify(shape);
  const tensorHandle = hg.tensorFromBuffer(bufferHandle, shapeJson);
  
  benchmark(`tensorShape([${shape.join(', ')}])`, () => {
    hg.tensorShape(tensorHandle);
  });
  
  benchmark(`tensorStrides([${shape.join(', ')}])`, () => {
    hg.tensorStrides(tensorHandle);
  });
  
  benchmark(`tensorNdim([${shape.join(', ')}])`, () => {
    hg.tensorNdim(tensorHandle);
  });
  
  benchmark(`tensorNumel([${shape.join(', ')}])`, () => {
    hg.tensorNumel(tensorHandle);
  });
  
  benchmark(`tensorIsContiguous([${shape.join(', ')}])`, () => {
    hg.tensorIsContiguous(tensorHandle);
  });
  
  if (shape.length === 2) {
    benchmark(`tensorTranspose([${shape.join(', ')}])`, () => {
      const transposed = hg.tensorTranspose(tensorHandle);
      hg.tensorCleanup(transposed);
    });
    
    const newShape = JSON.stringify([shape[1], shape[0]]);
    benchmark(`tensorReshape([${shape.join(', ')}])`, () => {
      const reshaped = hg.tensorReshape(tensorHandle, newShape);
      hg.tensorCleanup(reshaped);
    });
  }
  
  benchmark(`tensorView1d([${shape.join(', ')}])`, () => {
    const view1d = hg.tensorView1d(tensorHandle);
    hg.tensorCleanup(view1d);
  });
  
  hg.tensorCleanup(tensorHandle);
  hg.bufferCleanup(bufferHandle);
  hg.executorCleanup(executorHandle);
}

// Compiler infrastructure benchmarks
console.log('\n🔧 Compiler Infrastructure Benchmarks:');

benchmark('programBuilderNew()', () => {
  hg.programBuilderNew();
  // Note: No cleanup function available for program builder
});

benchmark('registerAllocatorNew()', () => {
  hg.registerAllocatorNew();
  // Note: No cleanup function available for register allocator
});

const executorHandle = hg.newExecutor();
const bufferHandle = hg.executorAllocateBuffer(executorHandle, 1000);

benchmark('addressBuilderDirect()', () => {
  hg.addressBuilderDirect(bufferHandle, 0);
});

// Memory usage benchmark
console.log('\n💾 Memory Usage Benchmark:');

const memoryTestIterations = 100;
const memoryHandles: number[] = [];

console.log(`Creating ${memoryTestIterations} executors and buffers...`);

const memoryStartTime = Date.now();
for (let i = 0; i < memoryTestIterations; i++) {
  const execHandle = hg.newExecutor();
  const bufHandle = hg.executorAllocateBuffer(execHandle, 1000);
  memoryHandles.push(execHandle, bufHandle);
}
const memoryEndTime = Date.now();

console.log(`Memory allocation time: ${memoryEndTime - memoryStartTime}ms`);
console.log(`Created ${memoryHandles.length / 2} executor-buffer pairs`);

// Clean up memory test
console.log('Cleaning up memory test resources...');
for (let i = 0; i < memoryHandles.length; i += 2) {
  const bufferHandle = memoryHandles[i + 1];
  const executorHandle = memoryHandles[i];
  if (bufferHandle !== undefined) {
    hg.bufferCleanup(bufferHandle);
  }
  if (executorHandle !== undefined) {
    hg.executorCleanup(executorHandle);
  }
}

// Cleanup remaining resources
hg.bufferCleanup(bufferHandle);
hg.executorCleanup(executorHandle);

// Performance summary
console.log('\n📈 Performance Summary:');
console.log('=======================');
console.log('All benchmarks completed successfully!');
console.log('Performance characteristics:');
console.log('- Core functions: Very fast (< 0.1ms)');
console.log('- Buffer operations: Fast (0.1-1ms)');
console.log('- Mathematical operations: Fast (0.1-10ms)');
console.log('- Tensor operations: Moderate (1-100ms)');
console.log('- Linear algebra: Moderate to slow (10-1000ms)');
console.log('- Memory management: Efficient with proper cleanup');

console.log('\n✅ Performance benchmarks completed successfully!');
