//! NOTE: All operations in this file are temporarily stubbed during Phase 0 migration.
//! They will be implemented with ISA Programs in Phase 1.

//! Sigmatics-Based Activation Functions (Zero-Overhead)
//!
//! This module provides neural network activation functions using
//! direct Sigmatics generator construction for canonical execution.
//!
//! # Architecture
//!
//! - **Zero-Overhead Execution**: Direct GeneratorCall construction (no parsing)
//! - Execute on 96-class ClassMemory
//! - Pattern-based canonicalization reduces operation count
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
//! use hologram_core::{Executor, ops::activation};
//!
//! let mut exec = Executor::new()?;
//! let mut input = exec.allocate::<f32>(3072)?;
//! let mut output = exec.allocate::<f32>(3072)?;
//!
//! // Apply sigmoid activation
//! activation::sigmoid(&mut exec, &input, &mut output, 3072)?;
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

static SIGMOID_CACHE: ProgramCache = ProgramCache::new();
static TANH_CACHE: ProgramCache = ProgramCache::new();
#[allow(dead_code)]
static SOFTMAX_CACHE: ProgramCache = ProgramCache::new();
static GELU_SCALAR_MUL1_CACHE: ProgramCache = ProgramCache::new();
static GELU_SCALAR_MUL2_CACHE: ProgramCache = ProgramCache::new();
static GELU_ADD_ONE_CACHE: ProgramCache = ProgramCache::new();
static GELU_SCALAR_MUL3_CACHE: ProgramCache = ProgramCache::new();
static SOFTMAX_SUB_MAX_CACHE: ProgramCache = ProgramCache::new();
static SOFTMAX_EXP_CACHE: ProgramCache = ProgramCache::new();
static SOFTMAX_DIV_CACHE: ProgramCache = ProgramCache::new();

// ============================================================================
// Activation Functions
// ============================================================================

/// Sigmoid activation: y[i] = 1 / (1 + exp(-x[i]))
///
/// Applies sigmoid activation function element-wise.
///
/// # Arguments
///
/// * `exec` - Executor for circuit execution
/// * `input` - Input buffer with N elements
/// * `output` - Output buffer (same size as input)
/// * `n` - Number of elements to process
///
/// # Example
///
/// ```text
/// let mut exec = Executor::new()?;
/// let mut input = exec.allocate::<f32>(100)?;
/// let mut output = exec.allocate::<f32>(100)?;
///
/// sigmoid(&mut exec, &input, &mut output, 100)?;
/// ```
#[tracing::instrument(skip(exec, input, output), fields(n = n))]
pub fn sigmoid<T: bytemuck::Pod>(
    exec: &mut Executor,
    input: &Buffer<T>,
    output: &mut Buffer<T>,
    n: usize,
) -> Result<()> {
    let start = std::time::Instant::now();

    if input.len() < n || output.len() < n {
        return Err(Error::InvalidOperation(format!(
            "Buffer too small: input.len()={}, output.len()={}, need={}",
            input.len(),
            output.len(),
            n
        )));
    }

    // Try inline kernel first for f32 and sizes <= 3072
    if std::any::type_name::<T>() == "f32" && n <= 3072 {
        if let Err(e) = try_inline_sigmoid(exec, input, output, n) {
            tracing::debug!("Inline kernel not available, falling back to Sigmatics: {}", e);
        } else {
            let metrics = ExecutionMetrics::new("sigmoid", n, start);
            metrics.log();
            return Ok(());
        }
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
            "sigmoid_phi",
            vec![class_input as u64, class_output as u64, n as u64, ty as u64],
        )
    } else {
        let handle_input = exec.get_buffer_handle(class_input)?.id();
        let handle_output = exec.get_buffer_handle(class_output)?.id();
        ProgramKey::new("sigmoid_buf", vec![handle_input, handle_output, n as u64, ty as u64])
    };

    // Get or create cached program
    let program = SIGMOID_CACHE.get_or_create(&cache_key, || {
        if use_phi {
            // PhiCoordinate path: cache-resident (5-10x speedup expected)
            tracing::debug!("Using PhiCoordinate addressing for cache-resident execution");
            crate::isa_builder::build_elementwise_unary_op_phi(class_input, class_output, n, ty, |dst, src| {
                hologram_backends::Instruction::SIGMOID { ty, dst, src }
            })
            .expect("Failed to build PhiCoordinate program")
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
            crate::isa_builder::build_elementwise_unary_op(handle_input, handle_output, n, ty, |dst, src| {
                hologram_backends::Instruction::SIGMOID { ty, dst, src }
            })
            .expect("Failed to build BufferOffset program")
        }
    });

    // Execute ISA program via backend
    let config = hologram_backends::LaunchConfig::default();
    exec.backend
        .write()
        .execute_program(&program, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    let metrics = ExecutionMetrics::new("sigmoid", n, start);
    metrics.log();

    Ok(())
}

/// Try to use inline kernel for sigmoid (f32 only)
fn try_inline_sigmoid<T: bytemuck::Pod>(
    _exec: &mut Executor,
    _input: &Buffer<T>,
    _output: &mut Buffer<T>,
    _n: usize,
) -> Result<()> {
    // Inline kernels require direct memory access which is no longer available
    // (ClassMemory has been removed). Fall back to ISA execution.
    Err(Error::InvalidOperation(
        "Inline kernels not available. Using ISA execution.".into(),
    ))
}

/// Tanh activation: y[i] = tanh(x[i])
///
/// Applies hyperbolic tangent activation function element-wise.
///
/// # Arguments
///
/// * `exec` - Executor for circuit execution
/// * `input` - Input buffer with N elements
/// * `output` - Output buffer (same size as input)
/// * `n` - Number of elements to process
///
/// # Example
///
/// ```text
/// let mut exec = Executor::new()?;
/// let mut input = exec.allocate::<f32>(100)?;
/// let mut output = exec.allocate::<f32>(100)?;
///
/// tanh(&mut exec, &input, &mut output, 100)?;
/// ```
#[tracing::instrument(skip(exec, input, output), fields(n = n))]
pub fn tanh<T: bytemuck::Pod>(exec: &mut Executor, input: &Buffer<T>, output: &mut Buffer<T>, n: usize) -> Result<()> {
    let start = std::time::Instant::now();

    if input.len() < n || output.len() < n {
        return Err(Error::InvalidOperation(format!(
            "Buffer too small: input.len()={}, output.len()={}, need={}",
            input.len(),
            output.len(),
            n
        )));
    }

    // Try inline kernel first for f32 and sizes <= 3072
    if std::any::type_name::<T>() == "f32" && n <= 3072 {
        if let Err(e) = try_inline_tanh(exec, input, output, n) {
            tracing::debug!("Inline kernel not available, falling back to Sigmatics: {}", e);
        } else {
            let metrics = ExecutionMetrics::new("tanh", n, start);
            metrics.log();
            return Ok(());
        }
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
            "tanh_phi",
            vec![class_input as u64, class_output as u64, n as u64, ty as u64],
        )
    } else {
        let handle_input = exec.get_buffer_handle(class_input)?.id();
        let handle_output = exec.get_buffer_handle(class_output)?.id();
        ProgramKey::new("tanh_buf", vec![handle_input, handle_output, n as u64, ty as u64])
    };

    // Get or create cached program
    let program = TANH_CACHE.get_or_create(&cache_key, || {
        if use_phi {
            // PhiCoordinate path: cache-resident (5-10x speedup expected)
            tracing::debug!("Using PhiCoordinate addressing for cache-resident execution");
            crate::isa_builder::build_elementwise_unary_op_phi(class_input, class_output, n, ty, |dst, src| {
                hologram_backends::Instruction::TANH { ty, dst, src }
            })
            .expect("Failed to build PhiCoordinate program")
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
            crate::isa_builder::build_elementwise_unary_op(handle_input, handle_output, n, ty, |dst, src| {
                hologram_backends::Instruction::TANH { ty, dst, src }
            })
            .expect("Failed to build BufferOffset program")
        }
    });

    // Execute ISA program via backend
    let config = hologram_backends::LaunchConfig::default();
    exec.backend
        .write()
        .execute_program(&program, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    let metrics = ExecutionMetrics::new("tanh", n, start);
    metrics.log();

    Ok(())
}

/// Try to use inline kernel for tanh (f32 only)
fn try_inline_tanh<T: bytemuck::Pod>(
    _exec: &mut Executor,
    _input: &Buffer<T>,
    _output: &mut Buffer<T>,
    _n: usize,
) -> Result<()> {
    // Inline kernels require direct memory access which is no longer available
    // (ClassMemory has been removed). Fall back to ISA execution.
    Err(Error::InvalidOperation(
        "Inline kernels not available. Using ISA execution.".into(),
    ))
}

/// GELU activation: y[i] = x[i] * Φ(x[i])
///
/// Applies Gaussian Error Linear Unit activation function.
/// Φ is the cumulative distribution function of the standard normal distribution.
///
/// # Arguments
///
/// * `exec` - Executor for circuit execution
/// * `input` - Input buffer with N elements
/// * `output` - Output buffer (same size as input)
/// * `n` - Number of elements to process
///
/// # Example
///
/// ```text
/// let mut exec = Executor::new()?;
/// let mut input = exec.allocate::<f32>(100)?;
/// let mut output = exec.allocate::<f32>(100)?;
///
/// gelu(&mut exec, &input, &mut output, 100)?;
/// ```
#[tracing::instrument(skip(exec, input, output), fields(n = n))]
pub fn gelu<T: bytemuck::Pod>(exec: &mut Executor, input: &Buffer<T>, output: &mut Buffer<T>, n: usize) -> Result<()> {
    let start = std::time::Instant::now();

    if input.len() < n || output.len() < n {
        return Err(Error::InvalidOperation(format!(
            "Buffer too small: input.len()={}, output.len()={}, need={}",
            input.len(),
            output.len(),
            n
        )));
    }

    // Try inline kernel first for f32 and sizes <= 3072
    if std::any::type_name::<T>() == "f32" && n <= 3072 {
        if let Err(e) = try_inline_gelu(exec, input, output, n) {
            tracing::debug!("Inline kernel not available, falling back to Sigmatics: {}", e);
        } else {
            let metrics = ExecutionMetrics::new("gelu", n, start);
            metrics.log();
            return Ok(());
        }
    }

    // GELU(x) ≈ 0.5 * x * (1 + tanh(√(2/π) * (x + 0.044715 * x³)))
    // √(2/π) ≈ 0.7978845608

    // Allocate temporary buffers
    let mut x_squared = exec.allocate::<T>(n)?;
    let mut x_cubed = exec.allocate::<T>(n)?;
    let term1 = exec.allocate::<T>(n)?; // 0.044715 * x³
    let mut term2 = exec.allocate::<T>(n)?; // x + 0.044715 * x³
    let term3 = exec.allocate::<T>(n)?; // √(2/π) * (x + 0.044715 * x³)
    let mut tanh_result = exec.allocate::<T>(n)?;
    let one_plus_tanh = exec.allocate::<T>(n)?;
    let mut x_times_result = exec.allocate::<T>(n)?;

    // Step 1: x² = x * x
    crate::ops::math::vector_mul(exec, input, input, &mut x_squared, n)?;

    // Step 2: x³ = x² * x
    crate::ops::math::vector_mul(exec, &x_squared, input, &mut x_cubed, n)?;

    // Step 3: term1 = 0.044715 * x³
    // Use ISA to multiply by scalar
    let class_x_cubed = x_cubed.class_index();
    let class_term1 = term1.class_index();
    let handle_x_cubed = exec.get_buffer_handle(class_x_cubed)?.id();
    let handle_term1 = exec.get_buffer_handle(class_term1)?.id();
    let ty = crate::isa_builder::type_from_rust_type::<T>();

    let coeff1_bits = if std::any::type_name::<T>() == "f32" {
        0.044715f32.to_bits() as u64
    } else if std::any::type_name::<T>() == "f64" {
        0.044715f64.to_bits()
    } else {
        return Err(Error::InvalidOperation("GELU only supports f32 and f64 types".into()));
    };

    let elem_size = ty.size_bytes();

    // Build cache key
    let cache_key = ProgramKey::new(
        "gelu_scalar_mul1",
        vec![handle_x_cubed, handle_term1, n as u64, ty as u64],
    );

    // Get or create cached program
    let scalar_mul_program = GELU_SCALAR_MUL1_CACHE.get_or_create(&cache_key, || {
        let mut program = hologram_backends::Program::new();
        for i in 0..n {
            let offset = i * elem_size;

            // Load coefficient
            program.instructions.push(hologram_backends::Instruction::MOV_IMM {
                ty,
                dst: hologram_backends::Register::new(1),
                value: coeff1_bits,
            });

            // Load x³[i]
            program.instructions.push(hologram_backends::Instruction::LDG {
                ty,
                dst: hologram_backends::Register::new(2),
                addr: hologram_backends::Address::BufferOffset {
                    handle: handle_x_cubed,
                    offset,
                },
            });

            // Multiply
            program.instructions.push(hologram_backends::Instruction::MUL {
                ty,
                dst: hologram_backends::Register::new(3),
                src1: hologram_backends::Register::new(1),
                src2: hologram_backends::Register::new(2),
            });

            // Store result
            program.instructions.push(hologram_backends::Instruction::STG {
                ty,
                src: hologram_backends::Register::new(3),
                addr: hologram_backends::Address::BufferOffset {
                    handle: handle_term1,
                    offset,
                },
            });
        }
        program
    });

    let config = hologram_backends::LaunchConfig::default();
    exec.backend
        .write()
        .execute_program(&scalar_mul_program, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    // Step 4: term2 = x + 0.044715 * x³
    crate::ops::math::vector_add(exec, input, &term1, &mut term2, n)?;

    // Step 5: term3 = √(2/π) * (x + 0.044715 * x³)
    let class_term2 = term2.class_index();
    let class_term3 = term3.class_index();
    let handle_term2 = exec.get_buffer_handle(class_term2)?.id();
    let handle_term3 = exec.get_buffer_handle(class_term3)?.id();

    let sqrt_2_pi_bits = if std::any::type_name::<T>() == "f32" {
        0.797_884_6_f32.to_bits() as u64
    } else {
        0.7978845608f64.to_bits()
    };

    // Build cache key
    let cache_key2 = ProgramKey::new(
        "gelu_scalar_mul2",
        vec![handle_term2, handle_term3, n as u64, ty as u64],
    );

    // Get or create cached program
    let scalar_mul_program2 = GELU_SCALAR_MUL2_CACHE.get_or_create(&cache_key2, || {
        let mut program = hologram_backends::Program::new();
        for i in 0..n {
            let offset = i * elem_size;

            program.instructions.push(hologram_backends::Instruction::MOV_IMM {
                ty,
                dst: hologram_backends::Register::new(1),
                value: sqrt_2_pi_bits,
            });

            program.instructions.push(hologram_backends::Instruction::LDG {
                ty,
                dst: hologram_backends::Register::new(2),
                addr: hologram_backends::Address::BufferOffset {
                    handle: handle_term2,
                    offset,
                },
            });

            program.instructions.push(hologram_backends::Instruction::MUL {
                ty,
                dst: hologram_backends::Register::new(3),
                src1: hologram_backends::Register::new(1),
                src2: hologram_backends::Register::new(2),
            });

            program.instructions.push(hologram_backends::Instruction::STG {
                ty,
                src: hologram_backends::Register::new(3),
                addr: hologram_backends::Address::BufferOffset {
                    handle: handle_term3,
                    offset,
                },
            });
        }
        program
    });

    exec.backend
        .write()
        .execute_program(&scalar_mul_program2, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    // Step 6: tanh_result = tanh(term3)
    tanh(exec, &term3, &mut tanh_result, n)?;

    // Step 7: one_plus_tanh = 1 + tanh_result
    let class_tanh = tanh_result.class_index();
    let class_one_plus = one_plus_tanh.class_index();
    let handle_tanh = exec.get_buffer_handle(class_tanh)?.id();
    let handle_one_plus = exec.get_buffer_handle(class_one_plus)?.id();

    let one_bits = if std::any::type_name::<T>() == "f32" {
        1.0f32.to_bits() as u64
    } else {
        1.0f64.to_bits()
    };

    // Build cache key
    let cache_key3 = ProgramKey::new("gelu_add_one", vec![handle_tanh, handle_one_plus, n as u64, ty as u64]);

    // Get or create cached program
    let add_one_program = GELU_ADD_ONE_CACHE.get_or_create(&cache_key3, || {
        let mut program = hologram_backends::Program::new();
        for i in 0..n {
            let offset = i * elem_size;

            program.instructions.push(hologram_backends::Instruction::MOV_IMM {
                ty,
                dst: hologram_backends::Register::new(1),
                value: one_bits,
            });

            program.instructions.push(hologram_backends::Instruction::LDG {
                ty,
                dst: hologram_backends::Register::new(2),
                addr: hologram_backends::Address::BufferOffset {
                    handle: handle_tanh,
                    offset,
                },
            });

            program.instructions.push(hologram_backends::Instruction::ADD {
                ty,
                dst: hologram_backends::Register::new(3),
                src1: hologram_backends::Register::new(1),
                src2: hologram_backends::Register::new(2),
            });

            program.instructions.push(hologram_backends::Instruction::STG {
                ty,
                src: hologram_backends::Register::new(3),
                addr: hologram_backends::Address::BufferOffset {
                    handle: handle_one_plus,
                    offset,
                },
            });
        }
        program
    });

    exec.backend
        .write()
        .execute_program(&add_one_program, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    // Step 8: x_times_result = x * (1 + tanh(...))
    crate::ops::math::vector_mul(exec, input, &one_plus_tanh, &mut x_times_result, n)?;

    // Step 9: output = 0.5 * x_times_result
    let class_x_times = x_times_result.class_index();
    let class_output = output.class_index();
    let handle_x_times = exec.get_buffer_handle(class_x_times)?.id();
    let handle_output = exec.get_buffer_handle(class_output)?.id();

    let half_bits = if std::any::type_name::<T>() == "f32" {
        0.5f32.to_bits() as u64
    } else {
        0.5f64.to_bits()
    };

    // Build cache key
    let cache_key4 = ProgramKey::new(
        "gelu_scalar_mul3",
        vec![handle_x_times, handle_output, n as u64, ty as u64],
    );

    // Get or create cached program
    let scalar_mul_program3 = GELU_SCALAR_MUL3_CACHE.get_or_create(&cache_key4, || {
        let mut program = hologram_backends::Program::new();
        for i in 0..n {
            let offset = i * elem_size;

            program.instructions.push(hologram_backends::Instruction::MOV_IMM {
                ty,
                dst: hologram_backends::Register::new(1),
                value: half_bits,
            });

            program.instructions.push(hologram_backends::Instruction::LDG {
                ty,
                dst: hologram_backends::Register::new(2),
                addr: hologram_backends::Address::BufferOffset {
                    handle: handle_x_times,
                    offset,
                },
            });

            program.instructions.push(hologram_backends::Instruction::MUL {
                ty,
                dst: hologram_backends::Register::new(3),
                src1: hologram_backends::Register::new(1),
                src2: hologram_backends::Register::new(2),
            });

            program.instructions.push(hologram_backends::Instruction::STG {
                ty,
                src: hologram_backends::Register::new(3),
                addr: hologram_backends::Address::BufferOffset {
                    handle: handle_output,
                    offset,
                },
            });
        }
        program
    });

    exec.backend
        .write()
        .execute_program(&scalar_mul_program3, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    let metrics = ExecutionMetrics::new("gelu", n, start);
    metrics.log();

    Ok(())
}

/// Try to use inline kernel for gelu (f32 only)
fn try_inline_gelu<T: bytemuck::Pod>(
    _exec: &mut Executor,
    _input: &Buffer<T>,
    _output: &mut Buffer<T>,
    _n: usize,
) -> Result<()> {
    // Inline kernels require direct memory access which is no longer available
    // (ClassMemory has been removed). Fall back to ISA execution.
    Err(Error::InvalidOperation(
        "Inline kernels not available. Using ISA execution.".into(),
    ))
}

/// Softmax activation: y[i] = exp(x[i]) / Σ exp(x[j])
///
/// Applies softmax activation function. Normalizes inputs to probability distribution.
///
/// # Arguments
///
/// * `exec` - Executor for circuit execution
/// * `input` - Input buffer with N elements
/// * `output` - Output buffer (same size as input)
/// * `n` - Number of elements to process
///
/// # Example
///
/// ```text
/// let mut exec = Executor::new()?;
/// let mut input = exec.allocate::<f32>(10)?;
/// let mut output = exec.allocate::<f32>(10)?;
///
/// softmax(&mut exec, &input, &mut output, 10)?;
/// // Output elements sum to 1.0
/// ```
#[tracing::instrument(skip(exec, input, output), fields(n = n))]
pub fn softmax<T: bytemuck::Pod>(
    exec: &mut Executor,
    input: &Buffer<T>,
    output: &mut Buffer<T>,
    n: usize,
) -> Result<()> {
    let start = std::time::Instant::now();

    if input.len() < n || output.len() < n {
        return Err(Error::InvalidOperation(format!(
            "Buffer too small: input.len()={}, output.len()={}, need={}",
            input.len(),
            output.len(),
            n
        )));
    }

    // Try inline kernel first for f32 and sizes <= 3072
    if std::any::type_name::<T>() == "f32" && n <= 3072 {
        if let Err(e) = try_inline_softmax(exec, input, output, n) {
            tracing::debug!("Inline kernel not available, falling back to Sigmatics: {}", e);
        } else {
            let metrics = ExecutionMetrics::new("softmax", n, start);
            metrics.log();
            return Ok(());
        }
    }

    // Softmax(x)_i = exp(x_i - max(x)) / Σ_j exp(x_j - max(x))
    // Use max subtraction for numerical stability

    // Step 1: Find max(x)
    let mut max_buf = exec.allocate::<T>(3)?; // Need 3 elements for reduction temporaries
    crate::ops::reduce::max(exec, input, &mut max_buf, n)?;
    let max_value = max_buf.to_vec(exec)?[0];

    // Step 2: Compute shifted = x - max (for numerical stability)
    let shifted = exec.allocate::<T>(n)?;

    // Subtract max from each element using ISA
    let class_input = input.class_index();
    let class_shifted = shifted.class_index();
    let handle_input = exec.get_buffer_handle(class_input)?.id();
    let handle_shifted = exec.get_buffer_handle(class_shifted)?.id();
    let ty = crate::isa_builder::type_from_rust_type::<T>();

    let max_bytes = bytemuck::bytes_of(&max_value);
    let max_bits = if std::any::type_name::<T>() == "f32" {
        u32::from_le_bytes([max_bytes[0], max_bytes[1], max_bytes[2], max_bytes[3]]) as u64
    } else if std::any::type_name::<T>() == "f64" {
        u64::from_le_bytes([
            max_bytes[0],
            max_bytes[1],
            max_bytes[2],
            max_bytes[3],
            max_bytes[4],
            max_bytes[5],
            max_bytes[6],
            max_bytes[7],
        ])
    } else {
        return Err(Error::InvalidOperation(
            "Softmax only supports f32 and f64 types".into(),
        ));
    };

    let elem_size = ty.size_bytes();

    // Build cache key
    let cache_key_sub = ProgramKey::new(
        "softmax_sub_max",
        vec![handle_input, handle_shifted, n as u64, ty as u64],
    );

    // Get or create cached program
    let sub_max_program = SOFTMAX_SUB_MAX_CACHE.get_or_create(&cache_key_sub, || {
        let mut program = hologram_backends::Program::new();
        for i in 0..n {
            let offset = i * elem_size;

            // Load x[i]
            program.instructions.push(hologram_backends::Instruction::LDG {
                ty,
                dst: hologram_backends::Register::new(1),
                addr: hologram_backends::Address::BufferOffset {
                    handle: handle_input,
                    offset,
                },
            });

            // Load max value
            program.instructions.push(hologram_backends::Instruction::MOV_IMM {
                ty,
                dst: hologram_backends::Register::new(2),
                value: max_bits,
            });

            // Subtract: r3 = r1 - r2
            program.instructions.push(hologram_backends::Instruction::SUB {
                ty,
                dst: hologram_backends::Register::new(3),
                src1: hologram_backends::Register::new(1),
                src2: hologram_backends::Register::new(2),
            });

            // Store shifted[i]
            program.instructions.push(hologram_backends::Instruction::STG {
                ty,
                src: hologram_backends::Register::new(3),
                addr: hologram_backends::Address::BufferOffset {
                    handle: handle_shifted,
                    offset,
                },
            });
        }
        program
    });

    let config = hologram_backends::LaunchConfig::default();
    exec.backend
        .write()
        .execute_program(&sub_max_program, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    // Step 3: Compute exp(shifted[i]) for each i
    let exp_values = exec.allocate::<T>(n)?;
    let class_exp = exp_values.class_index();
    let handle_exp = exec.get_buffer_handle(class_exp)?.id();

    // Build cache key
    let cache_key_exp = ProgramKey::new("softmax_exp", vec![handle_shifted, handle_exp, n as u64, ty as u64]);

    // Get or create cached program
    let exp_program = SOFTMAX_EXP_CACHE.get_or_create(&cache_key_exp, || {
        crate::isa_builder::build_elementwise_unary_op(handle_shifted, handle_exp, n, ty, |dst, src| {
            hologram_backends::Instruction::EXP { ty, dst, src }
        })
        .expect("Failed to build EXP program")
    });

    exec.backend
        .write()
        .execute_program(&exp_program, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    // Step 4: Sum all exp values
    let mut sum_buf = exec.allocate::<T>(3)?; // Need 3 elements for reduction temporaries
    crate::ops::reduce::sum(exec, &exp_values, &mut sum_buf, n)?;
    let sum_value = sum_buf.to_vec(exec)?[0];

    // Step 5: Divide each exp by the sum
    let sum_bytes = bytemuck::bytes_of(&sum_value);
    let sum_bits = if std::any::type_name::<T>() == "f32" {
        u32::from_le_bytes([sum_bytes[0], sum_bytes[1], sum_bytes[2], sum_bytes[3]]) as u64
    } else {
        u64::from_le_bytes([
            sum_bytes[0],
            sum_bytes[1],
            sum_bytes[2],
            sum_bytes[3],
            sum_bytes[4],
            sum_bytes[5],
            sum_bytes[6],
            sum_bytes[7],
        ])
    };

    let class_output = output.class_index();
    let handle_output = exec.get_buffer_handle(class_output)?.id();

    // Build cache key
    let cache_key_div = ProgramKey::new("softmax_div", vec![handle_exp, handle_output, n as u64, ty as u64]);

    // Get or create cached program
    let div_program = SOFTMAX_DIV_CACHE.get_or_create(&cache_key_div, || {
        let mut program = hologram_backends::Program::new();
        for i in 0..n {
            let offset = i * elem_size;

            // Load exp[i]
            program.instructions.push(hologram_backends::Instruction::LDG {
                ty,
                dst: hologram_backends::Register::new(1),
                addr: hologram_backends::Address::BufferOffset {
                    handle: handle_exp,
                    offset,
                },
            });

            // Load sum
            program.instructions.push(hologram_backends::Instruction::MOV_IMM {
                ty,
                dst: hologram_backends::Register::new(2),
                value: sum_bits,
            });

            // Divide: r3 = r1 / r2
            program.instructions.push(hologram_backends::Instruction::DIV {
                ty,
                dst: hologram_backends::Register::new(3),
                src1: hologram_backends::Register::new(1),
                src2: hologram_backends::Register::new(2),
            });

            // Store output[i]
            program.instructions.push(hologram_backends::Instruction::STG {
                ty,
                src: hologram_backends::Register::new(3),
                addr: hologram_backends::Address::BufferOffset {
                    handle: handle_output,
                    offset,
                },
            });
        }
        program
    });

    exec.backend
        .write()
        .execute_program(&div_program, &config)
        .map_err(|e| Error::InvalidOperation(format!("Backend execution failed: {}", e)))?;

    let metrics = ExecutionMetrics::new("softmax", n, start);
    metrics.log();

    Ok(())
}

/// Try to use inline kernel for softmax (f32 only)
fn try_inline_softmax<T: bytemuck::Pod>(
    _exec: &mut Executor,
    _input: &Buffer<T>,
    _output: &mut Buffer<T>,
    _n: usize,
) -> Result<()> {
    // Inline kernels require direct memory access which is no longer available
    // (ClassMemory has been removed). Fall back to ISA execution.
    Err(Error::InvalidOperation(
        "Inline kernels not available. Using ISA execution.".into(),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sigmoid() -> Result<()> {
        let mut exec = Executor::new()?;

        let mut input = exec.allocate::<f32>(100)?;
        let mut output = exec.allocate::<f32>(100)?;

        let data: Vec<f32> = (0..100).map(|i| i as f32 * 0.1).collect();
        input.copy_from_slice(&mut exec, &data)?;

        sigmoid(&mut exec, &input, &mut output, 100)?;

        // Note: actual sigmoid implementation TBD
        Ok(())
    }
}
