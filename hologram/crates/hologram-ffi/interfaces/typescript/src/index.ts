/**
 * Hologram FFI - TypeScript/Node.js bindings for Hologram Atlas runtime
 * 
 * This module provides TypeScript bindings for the Hologram Atlas computational interface,
 * enabling high-performance numerical computations across diverse hardware substrates.
 * 
 * @version 0.1.0
 * @author Hologram Project
 */

// Note: Native FFI bindings would be imported here when available
// import * as ffi from 'ffi-napi';
// import * as ref from 'ref-napi';

// Type definitions for handles
export type ExecutorHandle = number;
export type BufferHandle = number;
export type TensorHandle = number;
export type ProgramBuilderHandle = number;
export type RegisterAllocatorHandle = number;

// Error types
export enum FfiError {
  Hologram = 'Hologram',
  InvalidParameter = 'InvalidParameter',
  MemoryAllocation = 'MemoryAllocation',
  OperationFailed = 'OperationFailed',
  InternalError = 'InternalError',
  UnsupportedOperation = 'UnsupportedOperation',
  BufferError = 'BufferError',
  ExecutorError = 'ExecutorError',
  TensorError = 'TensorError',
  CompilerError = 'CompilerError'
}

// Native library interface
interface HologramFFILib {
  // Core Functions
  get_version(): string;
  get_executor_phase(): number;
  advance_executor_phase(delta: number): void;

  // Executor Management (Phase 1.1)
  new_executor(): ExecutorHandle;
  executor_with_backend(backend_type: string): ExecutorHandle;
  executor_allocate_buffer(executor_handle: ExecutorHandle, len: number): BufferHandle;
  executor_allocate_boundary_buffer(executor_handle: ExecutorHandle, classId: number, width: number, height: number): BufferHandle;
  executor_phase(executor_handle: ExecutorHandle): number;
  executor_advance_phase(executor_handle: ExecutorHandle, delta: number): void;
  executor_resonance_at(executor_handle: ExecutorHandle, classId: number): number;
  executor_resonance_snapshot(executor_handle: ExecutorHandle): string;
  executor_mirror(executor_handle: ExecutorHandle, classId: number): number;
  executor_neighbors(executor_handle: ExecutorHandle, classId: number): string;
  executor_cleanup(executor_handle: ExecutorHandle): void;

  // Buffer Operations (Phase 1.2)
  buffer_length(buffer_handle: BufferHandle): number;
  buffer_copy(src_handle: BufferHandle, dst_handle: BufferHandle, len: number): void;
  buffer_fill(buffer_handle: BufferHandle, value: number, len: number): void;
  buffer_to_vec(buffer_handle: BufferHandle): string;
  buffer_cleanup(buffer_handle: BufferHandle): void;

  // Additional Buffer Operations (Phase 2)
  buffer_backend_handle(buffer_handle: BufferHandle): BufferHandle;
  buffer_topology(buffer_handle: BufferHandle): string;
  buffer_is_empty(buffer_handle: BufferHandle): boolean;
  buffer_pool(buffer_handle: BufferHandle): string;
  buffer_is_linear(buffer_handle: BufferHandle): boolean;
  buffer_is_boundary(buffer_handle: BufferHandle): boolean;
  buffer_element_size(buffer_handle: BufferHandle): number;
  buffer_size_bytes(buffer_handle: BufferHandle): number;
  buffer_copy_from_slice(buffer_handle: BufferHandle, data_json: string): void;

  // Linear Algebra Operations (Phase 2.1)
  gemm_f32(m: number, n: number, k: number): void;
  matvec_f32(m: number, n: number): void;

  // Loss Functions (Phase 2.2)
  mse_loss_f32(len: number): number;
  cross_entropy_loss_f32(len: number): number;

  // Additional Math Operations (Phase 2.4)
  vector_min_f32(len: number): void;
  vector_max_f32(len: number): void;
  scalar_add_f32(value: number, len: number): void;
  scalar_mul_f32(value: number, len: number): void;
  gelu_f32(len: number): void;

  // Boundary Operations (Phase 2.5)
  transpose_boundary_f32(width: number, height: number): void;

  // Tensor Support (Phase 3.1)
  tensor_from_buffer(buffer_handle: BufferHandle, shape_json: string): TensorHandle;
  tensor_from_buffer_with_strides(buffer_handle: BufferHandle, shape_json: string, strides_json: string): TensorHandle;
  tensor_shape(tensor_handle: TensorHandle): string;
  tensor_strides(tensor_handle: TensorHandle): string;
  tensor_offset(tensor_handle: TensorHandle): number;
  tensor_ndim(tensor_handle: TensorHandle): number;
  tensor_numel(tensor_handle: TensorHandle): number;
  tensor_buffer(tensor_handle: TensorHandle): BufferHandle;
  tensor_is_contiguous(tensor_handle: TensorHandle): boolean;
  tensor_cleanup(tensor_handle: TensorHandle): void;

  // Tensor Operations (Phase 3.2)
  tensor_reshape(tensor_handle: TensorHandle, new_shape_json: string): TensorHandle;
  tensor_transpose(tensor_handle: TensorHandle): TensorHandle;
  tensor_permute(tensor_handle: TensorHandle, dims_json: string): TensorHandle;
  tensor_view_1d(tensor_handle: TensorHandle): TensorHandle;
  tensor_matmul(executor_handle: ExecutorHandle, tensor_a_handle: TensorHandle, tensor_b_handle: TensorHandle): TensorHandle;
  tensor_is_broadcast_compatible(tensor_a_handle: TensorHandle, tensor_b_handle: TensorHandle): boolean;
  tensor_broadcast_shape(tensor_a_handle: TensorHandle, tensor_b_handle: TensorHandle): string;
  tensor_select(tensor_handle: TensorHandle, dim: number, index: number): TensorHandle;
  tensor_narrow(tensor_handle: TensorHandle, dim: number, start: number, length: number): TensorHandle;
  tensor_slice(tensor_handle: TensorHandle, dim: number, start: number, end: number, step: number): TensorHandle;
  tensor_buffer_mut(tensor_handle: TensorHandle): BufferHandle;

  // Compiler Infrastructure (Phase 4)
  program_builder_new(): ProgramBuilderHandle;
  register_allocator_new(): RegisterAllocatorHandle;
  address_builder_direct(buffer_handle: BufferHandle, offset: number): string;

  // Atlas State Management (Phase 4.2)
  atlas_phase(): number;
  atlas_advance_phase(delta: number): void;
  atlas_resonance_at(classId: number): number;
  atlas_resonance_snapshot(): string;

  // Mathematical Operations (Simplified)
  vector_add_f32(len: number): void;
  vector_sub_f32(len: number): void;
  vector_mul_f32(len: number): void;
  vector_div_f32(len: number): void;
  vector_abs_f32(len: number): void;
  vector_neg_f32(len: number): void;
  vector_relu_f32(len: number): void;

  // Reduction Operations
  reduce_sum_f32(len: number): number;
  reduce_max_f32(len: number): number;
  reduce_min_f32(len: number): number;

  // Activation Functions
  sigmoid_f32(len: number): void;
  tanh_f32(len: number): void;
  softmax_f32(len: number): void;
}

// Load the native library
let hologramLib: HologramFFILib;

// For now, always use mock implementation
// In production, this would try to load the native library first
hologramLib = createMockLibrary();

/*
try {
  // Try to load the native library
  hologramLib = ffi.Library('./libhologram_ffi', {
    // Core Functions
    'get_version': ['string', []],
    'get_executor_phase': ['uint16', []],
    'advance_executor_phase': ['void', ['uint16']],

    // Executor Management (Phase 1.1)
    'new_executor': ['uint64', []],
    'executor_with_backend': ['uint64', ['string']],
    'executor_allocate_buffer': ['uint64', ['uint64', 'uint32']],
    'executor_allocate_boundary_buffer': ['uint64', ['uint64', 'uint8', 'uint32', 'uint32']],
    'executor_phase': ['uint16', ['uint64']],
    'executor_advance_phase': ['void', ['uint64', 'uint16']],
    'executor_resonance_at': ['double', ['uint64', 'uint8']],
    'executor_resonance_snapshot': ['string', ['uint64']],
    'executor_mirror': ['uint8', ['uint64', 'uint8']],
    'executor_neighbors': ['string', ['uint64', 'uint8']],
    'executor_cleanup': ['void', ['uint64']],

    // Buffer Operations (Phase 1.2)
    'buffer_length': ['uint32', ['uint64']],
    'buffer_copy': ['void', ['uint64', 'uint64', 'uint32']],
    'buffer_fill': ['void', ['uint64', 'float', 'uint32']],
    'buffer_to_vec': ['string', ['uint64']],
    'buffer_cleanup': ['void', ['uint64']],

    // Additional Buffer Operations (Phase 2)
    'buffer_backend_handle': ['uint64', ['uint64']],
    'buffer_topology': ['string', ['uint64']],
    'buffer_is_empty': ['bool', ['uint64']],
    'buffer_pool': ['string', ['uint64']],
    'buffer_is_linear': ['bool', ['uint64']],
    'buffer_is_boundary': ['bool', ['uint64']],
    'buffer_element_size': ['uint32', ['uint64']],
    'buffer_size_bytes': ['uint32', ['uint64']],
    'buffer_copy_from_slice': ['void', ['uint64', 'string']],

    // Linear Algebra Operations (Phase 2.1)
    'gemm_f32': ['void', ['uint32', 'uint32', 'uint32']],
    'matvec_f32': ['void', ['uint32', 'uint32']],

    // Loss Functions (Phase 2.2)
    'mse_loss_f32': ['float', ['uint32']],
    'cross_entropy_loss_f32': ['float', ['uint32']],

    // Additional Math Operations (Phase 2.4)
    'vector_min_f32': ['void', ['uint32']],
    'vector_max_f32': ['void', ['uint32']],
    'scalar_add_f32': ['void', ['float', 'uint32']],
    'scalar_mul_f32': ['void', ['float', 'uint32']],
    'gelu_f32': ['void', ['uint32']],

    // Boundary Operations (Phase 2.5)
    'transpose_boundary_f32': ['void', ['uint32', 'uint32']],

    // Tensor Support (Phase 3.1)
    'tensor_from_buffer': ['uint64', ['uint64', 'string']],
    'tensor_from_buffer_with_strides': ['uint64', ['uint64', 'string', 'string']],
    'tensor_shape': ['string', ['uint64']],
    'tensor_strides': ['string', ['uint64']],
    'tensor_offset': ['uint32', ['uint64']],
    'tensor_ndim': ['uint32', ['uint64']],
    'tensor_numel': ['uint32', ['uint64']],
    'tensor_buffer': ['uint64', ['uint64']],
    'tensor_is_contiguous': ['bool', ['uint64']],
    'tensor_cleanup': ['void', ['uint64']],

    // Tensor Operations (Phase 3.2)
    'tensor_reshape': ['uint64', ['uint64', 'string']],
    'tensor_transpose': ['uint64', ['uint64']],
    'tensor_permute': ['uint64', ['uint64', 'string']],
    'tensor_view_1d': ['uint64', ['uint64']],
    'tensor_matmul': ['uint64', ['uint64', 'uint64', 'uint64']],
    'tensor_is_broadcast_compatible': ['bool', ['uint64', 'uint64']],
    'tensor_broadcast_shape': ['string', ['uint64', 'uint64']],
    'tensor_select': ['uint64', ['uint64', 'uint32', 'uint32']],
    'tensor_narrow': ['uint64', ['uint64', 'uint32', 'uint32', 'uint32']],
    'tensor_slice': ['uint64', ['uint64', 'uint32', 'uint32', 'uint32', 'uint32']],
    'tensor_buffer_mut': ['uint64', ['uint64']],

    // Compiler Infrastructure (Phase 4)
    'program_builder_new': ['uint64', []],
    'register_allocator_new': ['uint64', []],
    'address_builder_direct': ['string', ['uint64', 'uint32']],

    // Atlas State Management (Phase 4.2)
    'atlas_phase': ['uint16', []],
    'atlas_advance_phase': ['void', ['uint16']],
    'atlas_resonance_at': ['double', ['uint8']],
    'atlas_resonance_snapshot': ['string', []],

    // Mathematical Operations (Simplified)
    'vector_add_f32': ['void', ['uint32']],
    'vector_sub_f32': ['void', ['uint32']],
    'vector_mul_f32': ['void', ['uint32']],
    'vector_div_f32': ['void', ['uint32']],
    'vector_abs_f32': ['void', ['uint32']],
    'vector_neg_f32': ['void', ['uint32']],
    'vector_relu_f32': ['void', ['uint32']],

    // Reduction Operations
    'reduce_sum_f32': ['float', ['uint32']],
    'reduce_max_f32': ['float', ['uint32']],
    'reduce_min_f32': ['float', ['uint32']],

    // Activation Functions
    'sigmoid_f32': ['void', ['uint32']],
    'tanh_f32': ['void', ['uint32']],
    'softmax_f32': ['void', ['uint32']],
  });
} catch (error) {
  console.warn('Failed to load native hologram-ffi library:', error);
  // Provide mock implementation for development
  hologramLib = createMockLibrary();
}
*/

function createMockLibrary(): HologramFFILib {
  // Mock implementation for development/testing
  return {
    // Core Functions
    get_version: () => '0.1.0-mock',
    get_executor_phase: () => 0,
    advance_executor_phase: () => {},

    // Executor Management (Phase 1.1)
    new_executor: () => 1,
    executor_with_backend: () => 2,
    executor_allocate_buffer: () => 3,
    executor_allocate_boundary_buffer: () => 4,
    executor_phase: () => 0,
    executor_advance_phase: () => {},
    executor_resonance_at: (_executorHandle: ExecutorHandle, _classId: number) => 0.5,
    executor_resonance_snapshot: (_executorHandle: ExecutorHandle) => '[]',
    executor_mirror: (_executorHandle: ExecutorHandle, _classId: number) => 0,
    executor_neighbors: (_executorHandle: ExecutorHandle, _classId: number) => '[]',
    executor_cleanup: () => {},

    // Buffer Operations (Phase 1.2)
    buffer_length: () => 0,
    buffer_copy: () => {},
    buffer_fill: () => {},
    buffer_to_vec: () => '[]',
    buffer_cleanup: () => {},

    // Additional Buffer Operations (Phase 2)
    buffer_backend_handle: () => 0,
    buffer_topology: () => '{}',
    buffer_is_empty: () => true,
    buffer_pool: () => 'linear',
    buffer_is_linear: () => true,
    buffer_is_boundary: () => false,
    buffer_element_size: () => 4,
    buffer_size_bytes: () => 0,
    buffer_copy_from_slice: () => {},

    // Linear Algebra Operations (Phase 2.1)
    gemm_f32: () => {},
    matvec_f32: () => {},

    // Loss Functions (Phase 2.2)
    mse_loss_f32: () => 0.0,
    cross_entropy_loss_f32: () => 0.0,

    // Additional Math Operations (Phase 2.4)
    vector_min_f32: () => {},
    vector_max_f32: () => {},
    scalar_add_f32: () => {},
    scalar_mul_f32: () => {},
    gelu_f32: () => {},

    // Boundary Operations (Phase 2.5)
    transpose_boundary_f32: () => {},

    // Tensor Support (Phase 3.1)
    tensor_from_buffer: () => 1,
    tensor_from_buffer_with_strides: () => 2,
    tensor_shape: () => '[]',
    tensor_strides: () => '[]',
    tensor_offset: () => 0,
    tensor_ndim: () => 0,
    tensor_numel: () => 0,
    tensor_buffer: () => 0,
    tensor_is_contiguous: () => true,
    tensor_cleanup: () => {},

    // Tensor Operations (Phase 3.2)
    tensor_reshape: () => 1,
    tensor_transpose: () => 2,
    tensor_permute: () => 3,
    tensor_view_1d: () => 4,
    tensor_matmul: () => 5,
    tensor_is_broadcast_compatible: () => true,
    tensor_broadcast_shape: () => '[]',
    tensor_select: () => 6,
    tensor_narrow: () => 7,
    tensor_slice: () => 8,
    tensor_buffer_mut: () => 9,

    // Compiler Infrastructure (Phase 4)
    program_builder_new: () => 1,
    register_allocator_new: () => 2,
    address_builder_direct: () => '{}',

    // Atlas State Management (Phase 4.2)
    atlas_phase: () => 0,
    atlas_advance_phase: () => {},
    atlas_resonance_at: (_classId: number) => 0.5,
    atlas_resonance_snapshot: () => '[]',

    // Mathematical Operations (Simplified)
    vector_add_f32: () => {},
    vector_sub_f32: () => {},
    vector_mul_f32: () => {},
    vector_div_f32: () => {},
    vector_abs_f32: () => {},
    vector_neg_f32: () => {},
    vector_relu_f32: () => {},

    // Reduction Operations
    reduce_sum_f32: () => 0.0,
    reduce_max_f32: () => 0.0,
    reduce_min_f32: () => 0.0,

    // Activation Functions
    sigmoid_f32: () => {},
    tanh_f32: () => {},
    softmax_f32: () => {},
  };
}

// Export all functions with proper TypeScript types
export const getVersion = (): string => hologramLib.get_version();
export const getExecutorPhase = (): number => hologramLib.get_executor_phase();
export const advanceExecutorPhase = (delta: number): void => hologramLib.advance_executor_phase(delta);

// Executor Management (Phase 1.1)
export const newExecutor = (): ExecutorHandle => hologramLib.new_executor();
export const executorWithBackend = (backendType: string): ExecutorHandle => hologramLib.executor_with_backend(backendType);
export const executorAllocateBuffer = (executorHandle: ExecutorHandle, len: number): BufferHandle => 
  hologramLib.executor_allocate_buffer(executorHandle, len);
export const executorAllocateBoundaryBuffer = (executorHandle: ExecutorHandle, classId: number, width: number, height: number): BufferHandle => 
  hologramLib.executor_allocate_boundary_buffer(executorHandle, classId, width, height);
export const executorPhase = (executorHandle: ExecutorHandle): number => hologramLib.executor_phase(executorHandle);
export const executorAdvancePhase = (executorHandle: ExecutorHandle, delta: number): void => 
  hologramLib.executor_advance_phase(executorHandle, delta);
export const executorResonanceAt = (executorHandle: ExecutorHandle, classId: number): number => 
  hologramLib.executor_resonance_at(executorHandle, classId);
export const executorResonanceSnapshot = (executorHandle: ExecutorHandle): string => 
  hologramLib.executor_resonance_snapshot(executorHandle);
export const executorMirror = (executorHandle: ExecutorHandle, classId: number): number => 
  hologramLib.executor_mirror(executorHandle, classId);
export const executorNeighbors = (executorHandle: ExecutorHandle, classId: number): string => 
  hologramLib.executor_neighbors(executorHandle, classId);
export const executorCleanup = (executorHandle: ExecutorHandle): void => hologramLib.executor_cleanup(executorHandle);

// Buffer Operations (Phase 1.2)
export const bufferLength = (bufferHandle: BufferHandle): number => hologramLib.buffer_length(bufferHandle);
export const bufferCopy = (srcHandle: BufferHandle, dstHandle: BufferHandle, len: number): void => 
  hologramLib.buffer_copy(srcHandle, dstHandle, len);
export const bufferFill = (bufferHandle: BufferHandle, value: number, len: number): void => 
  hologramLib.buffer_fill(bufferHandle, value, len);
export const bufferToVec = (bufferHandle: BufferHandle): string => hologramLib.buffer_to_vec(bufferHandle);
export const bufferCleanup = (bufferHandle: BufferHandle): void => hologramLib.buffer_cleanup(bufferHandle);

// Additional Buffer Operations (Phase 2)
export const bufferBackendHandle = (bufferHandle: BufferHandle): BufferHandle => 
  hologramLib.buffer_backend_handle(bufferHandle);
export const bufferTopology = (bufferHandle: BufferHandle): string => hologramLib.buffer_topology(bufferHandle);
export const bufferIsEmpty = (bufferHandle: BufferHandle): boolean => hologramLib.buffer_is_empty(bufferHandle);
export const bufferPool = (bufferHandle: BufferHandle): string => hologramLib.buffer_pool(bufferHandle);
export const bufferIsLinear = (bufferHandle: BufferHandle): boolean => hologramLib.buffer_is_linear(bufferHandle);
export const bufferIsBoundary = (bufferHandle: BufferHandle): boolean => hologramLib.buffer_is_boundary(bufferHandle);
export const bufferElementSize = (bufferHandle: BufferHandle): number => hologramLib.buffer_element_size(bufferHandle);
export const bufferSizeBytes = (bufferHandle: BufferHandle): number => hologramLib.buffer_size_bytes(bufferHandle);
export const bufferCopyFromSlice = (bufferHandle: BufferHandle, dataJson: string): void => 
  hologramLib.buffer_copy_from_slice(bufferHandle, dataJson);

// Linear Algebra Operations (Phase 2.1)
export const gemmF32 = (m: number, n: number, k: number): void => hologramLib.gemm_f32(m, n, k);
export const matvecF32 = (m: number, n: number): void => hologramLib.matvec_f32(m, n);

// Loss Functions (Phase 2.2)
export const mseLossF32 = (len: number): number => hologramLib.mse_loss_f32(len);
export const crossEntropyLossF32 = (len: number): number => hologramLib.cross_entropy_loss_f32(len);

// Additional Math Operations (Phase 2.4)
export const vectorMinF32 = (len: number): void => hologramLib.vector_min_f32(len);
export const vectorMaxF32 = (len: number): void => hologramLib.vector_max_f32(len);
export const scalarAddF32 = (value: number, len: number): void => hologramLib.scalar_add_f32(value, len);
export const scalarMulF32 = (value: number, len: number): void => hologramLib.scalar_mul_f32(value, len);
export const geluF32 = (len: number): void => hologramLib.gelu_f32(len);

// Boundary Operations (Phase 2.5)
export const transposeBoundaryF32 = (width: number, height: number): void => 
  hologramLib.transpose_boundary_f32(width, height);

// Tensor Support (Phase 3.1)
export const tensorFromBuffer = (bufferHandle: BufferHandle, shapeJson: string): TensorHandle => 
  hologramLib.tensor_from_buffer(bufferHandle, shapeJson);
export const tensorFromBufferWithStrides = (bufferHandle: BufferHandle, shapeJson: string, stridesJson: string): TensorHandle => 
  hologramLib.tensor_from_buffer_with_strides(bufferHandle, shapeJson, stridesJson);
export const tensorShape = (tensorHandle: TensorHandle): string => hologramLib.tensor_shape(tensorHandle);
export const tensorStrides = (tensorHandle: TensorHandle): string => hologramLib.tensor_strides(tensorHandle);
export const tensorOffset = (tensorHandle: TensorHandle): number => hologramLib.tensor_offset(tensorHandle);
export const tensorNdim = (tensorHandle: TensorHandle): number => hologramLib.tensor_ndim(tensorHandle);
export const tensorNumel = (tensorHandle: TensorHandle): number => hologramLib.tensor_numel(tensorHandle);
export const tensorBuffer = (tensorHandle: TensorHandle): BufferHandle => hologramLib.tensor_buffer(tensorHandle);
export const tensorIsContiguous = (tensorHandle: TensorHandle): boolean => hologramLib.tensor_is_contiguous(tensorHandle);
export const tensorCleanup = (tensorHandle: TensorHandle): void => hologramLib.tensor_cleanup(tensorHandle);

// Tensor Operations (Phase 3.2)
export const tensorReshape = (tensorHandle: TensorHandle, newShapeJson: string): TensorHandle => 
  hologramLib.tensor_reshape(tensorHandle, newShapeJson);
export const tensorTranspose = (tensorHandle: TensorHandle): TensorHandle => hologramLib.tensor_transpose(tensorHandle);
export const tensorPermute = (tensorHandle: TensorHandle, dimsJson: string): TensorHandle => 
  hologramLib.tensor_permute(tensorHandle, dimsJson);
export const tensorView1d = (tensorHandle: TensorHandle): TensorHandle => hologramLib.tensor_view_1d(tensorHandle);
export const tensorMatmul = (executorHandle: ExecutorHandle, tensorAHandle: TensorHandle, tensorBHandle: TensorHandle): TensorHandle => 
  hologramLib.tensor_matmul(executorHandle, tensorAHandle, tensorBHandle);
export const tensorIsBroadcastCompatible = (tensorAHandle: TensorHandle, tensorBHandle: TensorHandle): boolean => 
  hologramLib.tensor_is_broadcast_compatible(tensorAHandle, tensorBHandle);
export const tensorBroadcastShape = (tensorAHandle: TensorHandle, tensorBHandle: TensorHandle): string => 
  hologramLib.tensor_broadcast_shape(tensorAHandle, tensorBHandle);
export const tensorSelect = (tensorHandle: TensorHandle, dim: number, index: number): TensorHandle => 
  hologramLib.tensor_select(tensorHandle, dim, index);
export const tensorNarrow = (tensorHandle: TensorHandle, dim: number, start: number, length: number): TensorHandle => 
  hologramLib.tensor_narrow(tensorHandle, dim, start, length);
export const tensorSlice = (tensorHandle: TensorHandle, dim: number, start: number, end: number, step: number): TensorHandle => 
  hologramLib.tensor_slice(tensorHandle, dim, start, end, step);
export const tensorBufferMut = (tensorHandle: TensorHandle): BufferHandle => hologramLib.tensor_buffer_mut(tensorHandle);

// Compiler Infrastructure (Phase 4)
export const programBuilderNew = (): ProgramBuilderHandle => hologramLib.program_builder_new();
export const registerAllocatorNew = (): RegisterAllocatorHandle => hologramLib.register_allocator_new();
export const addressBuilderDirect = (bufferHandle: BufferHandle, offset: number): string => 
  hologramLib.address_builder_direct(bufferHandle, offset);

// Atlas State Management (Phase 4.2)
export const atlasPhase = (): number => hologramLib.atlas_phase();
export const atlasAdvancePhase = (delta: number): void => hologramLib.atlas_advance_phase(delta);
export const atlasResonanceAt = (classId: number): number => hologramLib.atlas_resonance_at(classId);
export const atlasResonanceSnapshot = (): string => hologramLib.atlas_resonance_snapshot();

// Mathematical Operations (Simplified)
export const vectorAddF32 = (len: number): void => hologramLib.vector_add_f32(len);
export const vectorSubF32 = (len: number): void => hologramLib.vector_sub_f32(len);
export const vectorMulF32 = (len: number): void => hologramLib.vector_mul_f32(len);
export const vectorDivF32 = (len: number): void => hologramLib.vector_div_f32(len);
export const vectorAbsF32 = (len: number): void => hologramLib.vector_abs_f32(len);
export const vectorNegF32 = (len: number): void => hologramLib.vector_neg_f32(len);
export const vectorReluF32 = (len: number): void => hologramLib.vector_relu_f32(len);

// Reduction Operations
export const reduceSumF32 = (len: number): number => hologramLib.reduce_sum_f32(len);
export const reduceMaxF32 = (len: number): number => hologramLib.reduce_max_f32(len);
export const reduceMinF32 = (len: number): number => hologramLib.reduce_min_f32(len);

// Activation Functions
export const sigmoidF32 = (len: number): void => hologramLib.sigmoid_f32(len);
export const tanhF32 = (len: number): void => hologramLib.tanh_f32(len);
export const softmaxF32 = (len: number): void => hologramLib.softmax_f32(len);

// Default export
export default {
  // Core Functions
  getVersion,
  getExecutorPhase,
  advanceExecutorPhase,

  // Executor Management (Phase 1.1)
  newExecutor,
  executorWithBackend,
  executorAllocateBuffer,
  executorAllocateBoundaryBuffer,
  executorPhase,
  executorAdvancePhase,
  executorResonanceAt,
  executorResonanceSnapshot,
  executorMirror,
  executorNeighbors,
  executorCleanup,

  // Buffer Operations (Phase 1.2)
  bufferLength,
  bufferCopy,
  bufferFill,
  bufferToVec,
  bufferCleanup,

  // Additional Buffer Operations (Phase 2)
  bufferBackendHandle,
  bufferTopology,
  bufferIsEmpty,
  bufferPool,
  bufferIsLinear,
  bufferIsBoundary,
  bufferElementSize,
  bufferSizeBytes,
  bufferCopyFromSlice,

  // Linear Algebra Operations (Phase 2.1)
  gemmF32,
  matvecF32,

  // Loss Functions (Phase 2.2)
  mseLossF32,
  crossEntropyLossF32,

  // Additional Math Operations (Phase 2.4)
  vectorMinF32,
  vectorMaxF32,
  scalarAddF32,
  scalarMulF32,
  geluF32,

  // Boundary Operations (Phase 2.5)
  transposeBoundaryF32,

  // Tensor Support (Phase 3.1)
  tensorFromBuffer,
  tensorFromBufferWithStrides,
  tensorShape,
  tensorStrides,
  tensorOffset,
  tensorNdim,
  tensorNumel,
  tensorBuffer,
  tensorIsContiguous,
  tensorCleanup,

  // Tensor Operations (Phase 3.2)
  tensorReshape,
  tensorTranspose,
  tensorPermute,
  tensorView1d,
  tensorMatmul,
  tensorIsBroadcastCompatible,
  tensorBroadcastShape,
  tensorSelect,
  tensorNarrow,
  tensorSlice,
  tensorBufferMut,

  // Compiler Infrastructure (Phase 4)
  programBuilderNew,
  registerAllocatorNew,
  addressBuilderDirect,

  // Atlas State Management (Phase 4.2)
  atlasPhase,
  atlasAdvancePhase,
  atlasResonanceAt,
  atlasResonanceSnapshot,

  // Mathematical Operations (Simplified)
  vectorAddF32,
  vectorSubF32,
  vectorMulF32,
  vectorDivF32,
  vectorAbsF32,
  vectorNegF32,
  vectorReluF32,

  // Reduction Operations
  reduceSumF32,
  reduceMaxF32,
  reduceMinF32,

  // Activation Functions
  sigmoidF32,
  tanhF32,
  softmaxF32,
};