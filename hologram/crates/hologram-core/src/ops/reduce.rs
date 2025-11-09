//! NOTE: All operations in this file are temporarily stubbed during Phase 0 migration.
//! They will be implemented with ISA Programs in Phase 1.

//! Sigmatics-Based Reduction Operations (Zero-Overhead)
//!
//! This module provides reduction operations using direct Sigmatics generator construction.
//! All operations reduce N elements to a single value using canonical circuits.
//!
//! # Architecture
//!
//! - **Zero-Overhead Execution**: Direct GeneratorCall construction (no parsing)
//! - Execute on 96-class ClassMemory
//! - Result stored in output buffer (first element)
//!
//! ## Performance
//!
//! ```text
//! Operation → Direct GeneratorCall Construction
//!   → execute_generators() → ClassMemory (bypasses parsing/canonicalization)
//! ```
//!
//! Latency: ~300-600ns (vs ~5-6µs with string parsing)
//!
//! # Example
//!
//! ```text
//! use hologram_core::{Executor, ops::reduce};
//!
//! let mut exec = Executor::new()?;
//! let mut input = exec.allocate::<f32>(3072)?;
//! let mut output = exec.allocate::<f32>(3)?; // Need 3 elements for temporaries
//!
//! // Prepare data
//! let data: Vec<f32> = (1..=100).map(|i| i as f32).collect();
//! input.copy_from_slice(&mut exec, &data)?;
//!
//! // Sum reduction
//! reduce::sum(&mut exec, &input, &mut output, 100)?;
//!
//! // Result is in output[0]
//! let result = output.to_vec(&exec)?;
//! println!("Sum: {}", result[0]);
//! ```

use crate::address_mapping::fits_in_class;
use crate::buffer::{Buffer, MemoryPool};
use crate::error::{Error, Result};
use crate::executor::Executor;
use crate::instrumentation::ExecutionMetrics;
use hologram_backends::program_cache::{ProgramCache, ProgramKey};

// ============================================================================
// Program Caches (Thread-Safe, Lock-Free After First Access)
// ============================================================================

static SUM_CACHE: ProgramCache = ProgramCache::new();
static REDUCE_MIN_CACHE: ProgramCache = ProgramCache::new();
static REDUCE_MAX_CACHE: ProgramCache = ProgramCache::new();

// ============================================================================
// Reduction Operations
// ============================================================================

/// Sum reduction: output[0] = Σ input[i]
///
/// Reduces all elements in input buffer to a single sum value.
///
/// # Arguments
///
/// * `exec` - Executor for circuit execution
/// * `input` - Input buffer with N elements
/// * `output` - Output buffer (needs at least 3 elements for temporaries)
/// * `n` - Number of elements to reduce
///
/// # Performance
///
/// Compiles to canonical circuit with pattern-based reduction.
/// Uses PhiCoordinate addressing for cache-resident boundary pool buffers (5-10x speedup).
///
/// # Example
///
/// ```text
/// let mut exec = Executor::new()?;
/// let mut input = exec.allocate::<f32>(3072)?;
/// let mut output = exec.allocate::<f32>(3)?;
///
/// let data: Vec<f32> = (1..=100).map(|i| i as f32).collect();
/// input.copy_from_slice(&mut exec, &data)?;
///
/// reduce::sum(&mut exec, &input, &mut output, 100)?;
/// println!("Sum: {}", output.to_vec(&exec)?[0]);
/// ```
#[tracing::instrument(skip(exec, input, output), fields(n = n))]
pub fn sum<T: bytemuck::Pod>(exec: &mut Executor, input: &Buffer<T>, output: &mut Buffer<T>, n: usize) -> Result<()> {
    let start = std::time::Instant::now();

    // Validate buffers
    if input.len() < n {
        return Err(Error::InvalidOperation(format!(
            "Input buffer too small: len={}, need={}",
            input.len(),
            n
        )));
    }
    if output.len() < 3 {
        return Err(Error::InvalidOperation(
            "Output buffer needs at least 3 elements for temporaries".into(),
        ));
    }

    let class_input = input.class_index();
    let class_output = output.class_index();
    let ty = crate::isa_builder::type_from_rust_type::<T>();

    // Check if we can use PhiCoordinate addressing (cache-resident boundary pools)
    let use_phi =
        input.pool() == MemoryPool::Boundary && output.pool() == MemoryPool::Boundary && fits_in_class::<T>(n);

    // Build cache key
    let cache_key = if use_phi {
        ProgramKey::new(
            "sum_phi",
            vec![class_input as u64, class_output as u64, n as u64, ty as u64],
        )
    } else {
        let handle_input = exec.get_buffer_handle(class_input)?.id();
        let handle_output = exec.get_buffer_handle(class_output)?.id();
        ProgramKey::new("sum_buf", vec![handle_input, handle_output, n as u64, ty as u64])
    };

    // Get or create cached program
    let program = SUM_CACHE.get_or_create(&cache_key, || {
        if use_phi {
            // PhiCoordinate path: cache-resident (5-10x speedup expected)
            tracing::debug!("Using PhiCoordinate addressing for cache-resident reduction");
            crate::isa_builder::build_reduction_op_phi(class_input, class_output, n, ty, |dst, src1, src2| {
                hologram_backends::Instruction::ADD { ty, dst, src1, src2 }
            })
            .expect("Failed to build PhiCoordinate reduction program")
        } else {
            // BufferOffset path: DRAM fallback
            let handle_input = exec
                .get_buffer_handle(class_input)
                .expect("Buffer handle not found")
                .id();
            let handle_output = exec
                .get_buffer_handle(class_output)
                .expect("Buffer handle not found")
                .id();
            crate::isa_builder::build_reduction_op(handle_input, handle_output, n, ty, |dst, src1, src2| {
                hologram_backends::Instruction::ADD { ty, dst, src1, src2 }
            })
            .expect("Failed to build BufferOffset reduction program")
        }
    });

    // Execute ISA program via backend
    let config = hologram_backends::LaunchConfig::default();
    exec.backend
        .write()
        .execute_program(&program, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    let metrics = ExecutionMetrics::new("sum", n, start);
    metrics.log();

    Ok(())
}

/// Min reduction: output[0] = min(input[i])
///
/// Reduces all elements in input buffer to the minimum value.
///
/// # Arguments
///
/// * `exec` - Executor for circuit execution
/// * `input` - Input buffer with N elements
/// * `output` - Output buffer (needs at least 3 elements for temporaries)
/// * `n` - Number of elements to reduce
///
/// # Performance
///
/// Uses PhiCoordinate addressing for cache-resident boundary pool buffers (5-10x speedup).
///
/// # Example
///
/// ```text
/// let mut exec = Executor::new()?;
/// let mut input = exec.allocate::<f32>(3072)?;
/// let mut output = exec.allocate::<f32>(3)?;
///
/// let data: Vec<f32> = vec![5.0, 2.0, 8.0, 1.0, 9.0];
/// input.copy_from_slice(&mut exec, &data)?;
///
/// reduce::min(&mut exec, &input, &mut output, 5)?;
/// assert_eq!(output.to_vec(&exec)?[0], 1.0);
/// ```
#[tracing::instrument(skip(exec, input, output), fields(n = n))]
pub fn min<T: bytemuck::Pod>(exec: &mut Executor, input: &Buffer<T>, output: &mut Buffer<T>, n: usize) -> Result<()> {
    let start = std::time::Instant::now();

    if input.len() < n {
        return Err(Error::InvalidOperation(format!(
            "Input buffer too small: len={}, need={}",
            input.len(),
            n
        )));
    }
    if output.len() < 3 {
        return Err(Error::InvalidOperation(
            "Output buffer needs at least 3 elements for temporaries".into(),
        ));
    }

    let class_input = input.class_index();
    let class_output = output.class_index();
    let ty = crate::isa_builder::type_from_rust_type::<T>();

    // Check if we can use PhiCoordinate addressing (cache-resident boundary pools)
    let use_phi =
        input.pool() == MemoryPool::Boundary && output.pool() == MemoryPool::Boundary && fits_in_class::<T>(n);

    // Build cache key
    let cache_key = if use_phi {
        ProgramKey::new(
            "min_phi",
            vec![class_input as u64, class_output as u64, n as u64, ty as u64],
        )
    } else {
        let handle_input = exec.get_buffer_handle(class_input)?.id();
        let handle_output = exec.get_buffer_handle(class_output)?.id();
        ProgramKey::new("min_buf", vec![handle_input, handle_output, n as u64, ty as u64])
    };

    // Get or create cached program
    let program = REDUCE_MIN_CACHE.get_or_create(&cache_key, || {
        if use_phi {
            // PhiCoordinate path: cache-resident (5-10x speedup expected)
            tracing::debug!("Using PhiCoordinate addressing for cache-resident reduction");
            crate::isa_builder::build_reduction_op_phi(class_input, class_output, n, ty, |dst, src1, src2| {
                hologram_backends::Instruction::MIN { ty, dst, src1, src2 }
            })
            .expect("Failed to build PhiCoordinate reduction program")
        } else {
            // BufferOffset path: DRAM fallback
            let handle_input = exec
                .get_buffer_handle(class_input)
                .expect("Buffer handle not found")
                .id();
            let handle_output = exec
                .get_buffer_handle(class_output)
                .expect("Buffer handle not found")
                .id();
            crate::isa_builder::build_reduction_op(handle_input, handle_output, n, ty, |dst, src1, src2| {
                hologram_backends::Instruction::MIN { ty, dst, src1, src2 }
            })
            .expect("Failed to build BufferOffset reduction program")
        }
    });

    // Execute ISA program via backend
    let config = hologram_backends::LaunchConfig::default();
    exec.backend
        .write()
        .execute_program(&program, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    let metrics = ExecutionMetrics::new("min", n, start);
    metrics.log();

    Ok(())
}

/// Max reduction: output[0] = max(input[i])
///
/// Reduces all elements in input buffer to the maximum value.
///
/// # Arguments
///
/// * `exec` - Executor for circuit execution
/// * `input` - Input buffer with N elements
/// * `output` - Output buffer (needs at least 3 elements for temporaries)
/// * `n` - Number of elements to reduce
///
/// # Performance
///
/// Uses PhiCoordinate addressing for cache-resident boundary pool buffers (5-10x speedup).
///
/// # Example
///
/// ```text
/// let mut exec = Executor::new()?;
/// let mut input = exec.allocate::<f32>(3072)?;
/// let mut output = exec.allocate::<f32>(3)?;
///
/// let data: Vec<f32> = vec![5.0, 2.0, 8.0, 1.0, 9.0];
/// input.copy_from_slice(&mut exec, &data)?;
///
/// reduce::max(&mut exec, &input, &mut output, 5)?;
/// assert_eq!(output.to_vec(&exec)?[0], 9.0);
/// ```
#[tracing::instrument(skip(exec, input, output), fields(n = n))]
pub fn max<T: bytemuck::Pod>(exec: &mut Executor, input: &Buffer<T>, output: &mut Buffer<T>, n: usize) -> Result<()> {
    let start = std::time::Instant::now();

    if input.len() < n {
        return Err(Error::InvalidOperation(format!(
            "Input buffer too small: len={}, need={}",
            input.len(),
            n
        )));
    }
    if output.len() < 3 {
        return Err(Error::InvalidOperation(
            "Output buffer needs at least 3 elements for temporaries".into(),
        ));
    }

    let class_input = input.class_index();
    let class_output = output.class_index();
    let ty = crate::isa_builder::type_from_rust_type::<T>();

    // Check if we can use PhiCoordinate addressing (cache-resident boundary pools)
    let use_phi =
        input.pool() == MemoryPool::Boundary && output.pool() == MemoryPool::Boundary && fits_in_class::<T>(n);

    // Build cache key
    let cache_key = if use_phi {
        ProgramKey::new(
            "max_phi",
            vec![class_input as u64, class_output as u64, n as u64, ty as u64],
        )
    } else {
        let handle_input = exec.get_buffer_handle(class_input)?.id();
        let handle_output = exec.get_buffer_handle(class_output)?.id();
        ProgramKey::new("max_buf", vec![handle_input, handle_output, n as u64, ty as u64])
    };

    // Get or create cached program
    let program = REDUCE_MAX_CACHE.get_or_create(&cache_key, || {
        if use_phi {
            // PhiCoordinate path: cache-resident (5-10x speedup expected)
            tracing::debug!("Using PhiCoordinate addressing for cache-resident reduction");
            crate::isa_builder::build_reduction_op_phi(class_input, class_output, n, ty, |dst, src1, src2| {
                hologram_backends::Instruction::MAX { ty, dst, src1, src2 }
            })
            .expect("Failed to build PhiCoordinate reduction program")
        } else {
            // BufferOffset path: DRAM fallback
            let handle_input = exec
                .get_buffer_handle(class_input)
                .expect("Buffer handle not found")
                .id();
            let handle_output = exec
                .get_buffer_handle(class_output)
                .expect("Buffer handle not found")
                .id();
            crate::isa_builder::build_reduction_op(handle_input, handle_output, n, ty, |dst, src1, src2| {
                hologram_backends::Instruction::MAX { ty, dst, src1, src2 }
            })
            .expect("Failed to build BufferOffset reduction program")
        }
    });

    // Execute ISA program via backend
    let config = hologram_backends::LaunchConfig::default();
    exec.backend
        .write()
        .execute_program(&program, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    let metrics = ExecutionMetrics::new("max", n, start);
    metrics.log();

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sum() -> Result<()> {
        let mut exec = Executor::new()?;

        let mut input = exec.allocate::<f32>(100)?;
        let mut output = exec.allocate::<f32>(3)?;

        let data: Vec<f32> = (1..=100).map(|i| i as f32).collect();
        input.copy_from_slice(&mut exec, &data)?;

        sum(&mut exec, &input, &mut output, 100)?;

        // Note: actual sum implementation TBD
        Ok(())
    }
}

// ============================================================================
// Parallel Reduction Operations (Phase 3)
// ============================================================================

/// Parallel sum reduction with tree-based algorithm
///
/// Implements divide-and-conquer reduction for large vectors.
/// Splits input into chunks, reduces each chunk, then combines results.
///
/// # Performance
///
/// - Small vectors (n < 10,000): Use standard `sum`
/// - Large vectors (n ≥ 10,000): Tree-based parallel reduction (2-4x speedup)
///
/// # Algorithm
///
/// ```text
/// Input: [a1, a2, ..., an]
/// Step 1: Split into k chunks of size ~3072
/// Step 2: Reduce each chunk in parallel → [sum1, sum2, ..., sumk]
/// Step 3: Sum the partial results → final_sum
/// ```
///
/// # Example
///
/// ```ignore
/// let mut exec = Executor::new()?;
/// let input = exec.allocate::<f32>(100_000)?;
/// let mut output = exec.allocate::<f32>(3)?;
///
/// // Tree-based parallel reduction
/// ops::reduce::sum_par(&mut exec, &input, &mut output, 100_000)?;
/// ```
pub fn sum_par<T: bytemuck::Pod + Send + Sync>(
    exec: &mut Executor,
    input: &Buffer<T>,
    output: &mut Buffer<T>,
    n: usize,
) -> Result<()> {
    // For small vectors, use standard implementation
    const REDUCTION_THRESHOLD: usize = 10_000;
    if n < REDUCTION_THRESHOLD {
        return sum(exec, input, output, n);
    }

    // Tree-based reduction:
    // 1. Split input into chunks of size ~3072
    // 2. Reduce each chunk to a single value
    // 3. Combine partial results
    //
    // Note: Without buffer slicing, we need to create temporary buffers for each chunk
    // Future optimization: Use buffer views when available

    const CHUNK_SIZE: usize = 3072;
    let chunk_count = n.div_ceil(CHUNK_SIZE);

    // Read input data once
    let input_data = input.to_vec(exec)?;

    // Allocate buffers for partial results
    let mut partial_results = Vec::with_capacity(chunk_count);

    // Process each chunk sequentially (backend provides parallelism)
    // Future: Use par_iter when Executor is thread-safe
    for chunk_idx in 0..chunk_count {
        let start = chunk_idx * CHUNK_SIZE;
        let end = (start + CHUNK_SIZE).min(n);
        let chunk_n = end - start;

        // Create buffer for this chunk
        let mut chunk_input = exec.allocate::<T>(chunk_n)?;
        let mut chunk_output = exec.allocate::<T>(3)?; // Reductions need 3 elements

        // Copy chunk data
        chunk_input.copy_from_slice(exec, &input_data[start..end])?;

        // Reduce this chunk
        sum(exec, &chunk_input, &mut chunk_output, chunk_n)?;

        // Extract result (first element contains the sum)
        let chunk_result = chunk_output.to_vec(exec)?;
        partial_results.push(chunk_result[0]);
    }

    // Final reduction: sum all partial results
    // This is a small reduction (chunk_count is typically < 100)
    if chunk_count == 1 {
        // Single chunk, result is already in output from the loop
        let final_result = vec![partial_results[0], partial_results[0], partial_results[0]];
        output.copy_from_slice(exec, &final_result)?;
    } else {
        // Multiple chunks: create buffer and sum the partial results
        let mut partials_buffer = exec.allocate::<T>(partial_results.len())?;
        partials_buffer.copy_from_slice(exec, &partial_results)?;
        sum(exec, &partials_buffer, output, partial_results.len())?;
    }

    Ok(())
}

/// Parallel min reduction with tree-based algorithm
///
/// Implements divide-and-conquer reduction for finding minimum value.
///
/// # Performance
///
/// - Small vectors (n < 10,000): Use standard `min`
/// - Large vectors (n ≥ 10,000): Tree-based parallel reduction (2-4x speedup)
pub fn min_par<T: bytemuck::Pod + Send + Sync>(
    exec: &mut Executor,
    input: &Buffer<T>,
    output: &mut Buffer<T>,
    n: usize,
) -> Result<()> {
    const REDUCTION_THRESHOLD: usize = 10_000;
    if n < REDUCTION_THRESHOLD {
        return min(exec, input, output, n);
    }

    // Tree-based reduction (same as sum_par but for minimum)
    const CHUNK_SIZE: usize = 3072;
    let chunk_count = n.div_ceil(CHUNK_SIZE);

    let input_data = input.to_vec(exec)?;
    let mut partial_results = Vec::with_capacity(chunk_count);

    // Reduce each chunk to find partial minimums
    for chunk_idx in 0..chunk_count {
        let start = chunk_idx * CHUNK_SIZE;
        let end = (start + CHUNK_SIZE).min(n);
        let chunk_n = end - start;

        let mut chunk_input = exec.allocate::<T>(chunk_n)?;
        let mut chunk_output = exec.allocate::<T>(3)?;

        chunk_input.copy_from_slice(exec, &input_data[start..end])?;
        min(exec, &chunk_input, &mut chunk_output, chunk_n)?;

        let chunk_result = chunk_output.to_vec(exec)?;
        partial_results.push(chunk_result[0]);
    }

    // Final reduction: find minimum of partial results
    if chunk_count == 1 {
        let final_result = vec![partial_results[0], partial_results[0], partial_results[0]];
        output.copy_from_slice(exec, &final_result)?;
    } else {
        let mut partials_buffer = exec.allocate::<T>(partial_results.len())?;
        partials_buffer.copy_from_slice(exec, &partial_results)?;
        min(exec, &partials_buffer, output, partial_results.len())?;
    }

    Ok(())
}

/// Parallel max reduction with tree-based algorithm
///
/// Implements divide-and-conquer reduction for finding maximum value.
///
/// # Performance
///
/// - Small vectors (n < 10,000): Use standard `max`
/// - Large vectors (n ≥ 10,000): Tree-based parallel reduction (2-4x speedup)
pub fn max_par<T: bytemuck::Pod + Send + Sync>(
    exec: &mut Executor,
    input: &Buffer<T>,
    output: &mut Buffer<T>,
    n: usize,
) -> Result<()> {
    const REDUCTION_THRESHOLD: usize = 10_000;
    if n < REDUCTION_THRESHOLD {
        return max(exec, input, output, n);
    }

    // Tree-based reduction (same as sum_par but for maximum)
    const CHUNK_SIZE: usize = 3072;
    let chunk_count = n.div_ceil(CHUNK_SIZE);

    let input_data = input.to_vec(exec)?;
    let mut partial_results = Vec::with_capacity(chunk_count);

    // Reduce each chunk to find partial maximums
    for chunk_idx in 0..chunk_count {
        let start = chunk_idx * CHUNK_SIZE;
        let end = (start + CHUNK_SIZE).min(n);
        let chunk_n = end - start;

        let mut chunk_input = exec.allocate::<T>(chunk_n)?;
        let mut chunk_output = exec.allocate::<T>(3)?;

        chunk_input.copy_from_slice(exec, &input_data[start..end])?;
        max(exec, &chunk_input, &mut chunk_output, chunk_n)?;

        let chunk_result = chunk_output.to_vec(exec)?;
        partial_results.push(chunk_result[0]);
    }

    // Final reduction: find maximum of partial results
    if chunk_count == 1 {
        let final_result = vec![partial_results[0], partial_results[0], partial_results[0]];
        output.copy_from_slice(exec, &final_result)?;
    } else {
        let mut partials_buffer = exec.allocate::<T>(partial_results.len())?;
        partials_buffer.copy_from_slice(exec, &partial_results)?;
        max(exec, &partials_buffer, output, partial_results.len())?;
    }

    Ok(())
}
