//! Memory operations
//!
//! This module provides memory manipulation operations:
//! - Buffer-to-buffer copy
//! - Buffer fill with constant value
//!
//! # Example
//!
//! ```text
//! use hologram_core::{Executor, ops::memory};
//!
//! let mut exec = Executor::new()?;
//! let src = exec.allocate::<f32>(3072)?;
//! let mut dst = exec.allocate::<f32>(3072)?;
//!
//! // Copy data
//! memory::copy(&mut exec, &src, &mut dst)?;
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

static COPY_CACHE: ProgramCache = ProgramCache::new();
static FILL_CACHE: ProgramCache = ProgramCache::new();

// ============================================================================
// Memory Operations
// ============================================================================

/// Copy buffer contents: dst = src
///
/// Copies data from source buffer to destination buffer.
///
/// ISA-based implementation using LDG/STG instructions for direct buffer-to-buffer transfer.
///
/// # Arguments
///
/// * `exec` - Executor for buffer access
/// * `src` - Source buffer
/// * `dst` - Destination buffer (must be same size as src)
///
/// # Example
///
/// ```text
/// let mut exec = Executor::new()?;
/// let src = exec.allocate::<f32>(3072)?;
/// let mut dst = exec.allocate::<f32>(3072)?;
///
/// copy(&mut exec, &src, &mut dst)?;
/// ```
#[tracing::instrument(skip(exec, src, dst), fields(
    len = src.len(),
    elem_size = std::mem::size_of::<T>(),
    type_name = std::any::type_name::<T>()
))]
pub fn copy<T: bytemuck::Pod>(exec: &mut Executor, src: &Buffer<T>, dst: &mut Buffer<T>) -> Result<()> {
    let start = std::time::Instant::now();
    let n = src.len();

    if n != dst.len() {
        return Err(Error::InvalidOperation(format!(
            "Buffer size mismatch: src.len()={}, dst.len()={}",
            n,
            dst.len()
        )));
    }

    // ISA-based implementation using Atlas ISA Program
    let class_src = src.class_index();
    let class_dst = dst.class_index();
    let ty = crate::isa_builder::type_from_rust_type::<T>();

    // Check if we can use PhiCoordinate addressing (cache-resident boundary pools)
    let use_phi = src.pool() == MemoryPool::Boundary && dst.pool() == MemoryPool::Boundary && fits_in_class::<T>(n);

    // Build cache key (value is not included for copy - it's a buffer parameter)
    let cache_key = if use_phi {
        ProgramKey::new(
            "copy_phi",
            vec![class_src as u64, class_dst as u64, n as u64, ty as u64],
        )
    } else {
        let handle_src = exec.get_buffer_handle(class_src)?.id();
        let handle_dst = exec.get_buffer_handle(class_dst)?.id();
        ProgramKey::new("copy_buf", vec![handle_src, handle_dst, n as u64, ty as u64])
    };

    // Get or create cached program
    let program = COPY_CACHE.get_or_create(&cache_key, || {
        if use_phi {
            tracing::debug!("Using PhiCoordinate addressing for cache-resident execution");
            crate::isa_builder::build_copy_op_phi(class_src, class_dst, n, ty)
                .expect("Failed to build PhiCoordinate copy program")
        } else {
            let handle_src = exec.get_buffer_handle(class_src).expect("Buffer handle not found").id();
            let handle_dst = exec.get_buffer_handle(class_dst).expect("Buffer handle not found").id();
            crate::isa_builder::build_copy_op(handle_src, handle_dst, n, ty)
                .expect("Failed to build BufferOffset copy program")
        }
    });

    // Execute ISA program via backend
    let config = hologram_backends::LaunchConfig::default();
    exec.backend
        .write()
        .execute_program(&program, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    // Instrumentation
    let metrics = ExecutionMetrics::new("copy", n, start);
    metrics.log();

    tracing::debug!(
        duration_us = metrics.total_duration_us,
        ops_per_second = metrics.ops_per_second(),
        memory_bandwidth_gbps = metrics.memory_bandwidth_gbps(),
        "copy_complete"
    );

    Ok(())
}

/// Fill buffer with value: buf[i] = value
///
/// Fills all elements in buffer with a constant value.
///
/// ISA-based implementation using MOV_IMM and STG instructions.
///
/// # Arguments
///
/// * `exec` - Executor for circuit execution
/// * `buf` - Buffer to fill
/// * `value` - Value to fill with
///
/// # Example
///
/// ```text
/// let mut exec = Executor::new()?;
/// let mut buf = exec.allocate::<f32>(3072)?;
///
/// fill(&mut exec, &mut buf, 42.0f32)?;
/// // All elements are now 42.0
/// ```
#[tracing::instrument(skip(exec, buf), fields(
    len = buf.len(),
    elem_size = std::mem::size_of::<T>(),
    type_name = std::any::type_name::<T>()
))]
pub fn fill<T: bytemuck::Pod + Copy + std::fmt::Debug>(
    exec: &mut Executor,
    buf: &mut Buffer<T>,
    value: T,
) -> Result<()> {
    let start = std::time::Instant::now();
    let n = buf.len();

    // ISA-based implementation using Atlas ISA Program
    let class_buf = buf.class_index();
    let ty = crate::isa_builder::type_from_rust_type::<T>();

    // Convert value to u64 for MOV_IMM instruction
    let value_bytes = bytemuck::bytes_of(&value);
    let value_u64 = if value_bytes.len() <= 8 {
        let mut buf = [0u8; 8];
        buf[..value_bytes.len()].copy_from_slice(value_bytes);
        u64::from_le_bytes(buf)
    } else {
        return Err(Error::InvalidOperation(format!(
            "Type too large for immediate value: {} bytes",
            value_bytes.len()
        )));
    };

    // Check if we can use PhiCoordinate addressing (cache-resident boundary pools)
    let use_phi = buf.pool() == MemoryPool::Boundary && fits_in_class::<T>(n);

    // Build cache key (value is immediate, not included in cache key - each fill creates new program)
    // Note: For fill, we DON'T include value in cache key because MOV_IMM embeds the value
    let cache_key = if use_phi {
        ProgramKey::new("fill_phi", vec![class_buf as u64, n as u64, ty as u64, value_u64])
    } else {
        let handle_buf = exec.get_buffer_handle(class_buf)?.id();
        ProgramKey::new("fill_buf", vec![handle_buf, n as u64, ty as u64, value_u64])
    };

    // Get or create cached program
    let program = FILL_CACHE.get_or_create(&cache_key, || {
        if use_phi {
            tracing::debug!("Using PhiCoordinate addressing for cache-resident execution");
            crate::isa_builder::build_fill_op_phi(class_buf, n, ty, value_u64)
                .expect("Failed to build PhiCoordinate fill program")
        } else {
            let handle_buf = exec.get_buffer_handle(class_buf).expect("Buffer handle not found").id();
            crate::isa_builder::build_fill_op(handle_buf, n, ty, value_u64)
                .expect("Failed to build BufferOffset fill program")
        }
    });

    // Execute ISA program via backend
    let config = hologram_backends::LaunchConfig::default();
    exec.backend
        .write()
        .execute_program(&program, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    // Instrumentation
    let metrics = ExecutionMetrics::new("fill", n, start);
    metrics.log();

    tracing::debug!(
        duration_us = metrics.total_duration_us,
        ops_per_second = metrics.ops_per_second(),
        memory_bandwidth_gbps = metrics.memory_bandwidth_gbps(),
        "fill_complete"
    );

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_copy() -> Result<()> {
        let mut exec = Executor::new()?;

        let mut src = exec.allocate::<f32>(100)?;
        let mut dst = exec.allocate::<f32>(100)?;

        let data: Vec<f32> = (0..100).map(|i| i as f32).collect();
        src.copy_from_slice(&mut exec, &data)?;

        copy(&mut exec, &src, &mut dst)?;

        let result = dst.to_vec(&exec)?;
        assert_eq!(result[0], 0.0);
        assert_eq!(result[99], 99.0);

        Ok(())
    }

    #[test]
    fn test_fill() -> Result<()> {
        let mut exec = Executor::new()?;

        let mut buf = exec.allocate::<f32>(100)?;

        fill(&mut exec, &mut buf, 42.0f32)?;

        let result = buf.to_vec(&exec)?;
        assert!(result.iter().all(|&x| x == 42.0));

        Ok(())
    }
}
