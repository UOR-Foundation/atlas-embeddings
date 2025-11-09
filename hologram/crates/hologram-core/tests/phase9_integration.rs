//! Phase 9 Integration Tests for Hologram-Core
//!
//! Comprehensive integration tests for all hologram-core operations
//! with multi-type support and large buffer scenarios.
//!
//! **NOTE**: These tests are currently marked as #[ignore] pending ISA Program migration.
//! The operations still use SigmaticsCompiler placeholders which need to be
//! replaced with precompiled ISA Programs before these tests can run.
//!
//! To enable these tests once migration is complete, remove the #[ignore] attributes.

use hologram_core::{ops, Executor, Result};

// Load kernels once at the start
static KERNELS_LOADED: std::sync::Once = std::sync::Once::new();
fn ensure_kernels_loaded() {
    KERNELS_LOADED.call_once(|| {
        use hologram_codegen::register_all_kernels_from_directory;
        match register_all_kernels_from_directory("../../target/kernel-libs") {
            Ok(kernels) => println!("✅ Loaded {} kernels", kernels.len()),
            Err(e) => println!("⚠️  Could not load kernels: {} (tests will use Sigmatics fallback)", e),
        }
    });
}

// ============================================================================
// ops::math Integration Tests (Task 4.3 - All 12 operations)
// ============================================================================

#[test]
fn test_math_vector_add_multi_types() -> Result<()> {
    ensure_kernels_loaded();
    let mut exec = Executor::new()?;

    // Test with F32
    let a = exec.allocate::<f32>(1024)?;
    let b = exec.allocate::<f32>(1024)?;
    let mut c = exec.allocate::<f32>(1024)?;

    ops::math::vector_add(&mut exec, &a, &b, &mut c, 1024)?;

    // Test with I32
    let a_i32 = exec.allocate::<i32>(1024)?;
    let b_i32 = exec.allocate::<i32>(1024)?;
    let mut c_i32 = exec.allocate::<i32>(1024)?;

    ops::math::vector_add(&mut exec, &a_i32, &b_i32, &mut c_i32, 1024)?;

    // Test with F64
    let a_f64 = exec.allocate::<f64>(1024)?;
    let b_f64 = exec.allocate::<f64>(1024)?;
    let mut c_f64 = exec.allocate::<f64>(1024)?;

    ops::math::vector_add(&mut exec, &a_f64, &b_f64, &mut c_f64, 1024)?;

    Ok(())
}

#[test]
fn test_math_vector_sub_multi_types() -> Result<()> {
    let mut exec = Executor::new()?;

    let a = exec.allocate::<f32>(512)?;
    let b = exec.allocate::<f32>(512)?;
    let mut c = exec.allocate::<f32>(512)?;

    ops::math::vector_sub(&mut exec, &a, &b, &mut c, 512)?;

    // Test with I32
    let a_i32 = exec.allocate::<i32>(512)?;
    let b_i32 = exec.allocate::<i32>(512)?;
    let mut c_i32 = exec.allocate::<i32>(512)?;

    ops::math::vector_sub(&mut exec, &a_i32, &b_i32, &mut c_i32, 512)?;

    Ok(())
}

#[test]
fn test_math_vector_mul_multi_types() -> Result<()> {
    let mut exec = Executor::new()?;

    let a = exec.allocate::<f32>(256)?;
    let b = exec.allocate::<f32>(256)?;
    let mut c = exec.allocate::<f32>(256)?;

    ops::math::vector_mul(&mut exec, &a, &b, &mut c, 256)?;

    // Test with U32
    let a_u32 = exec.allocate::<u32>(256)?;
    let b_u32 = exec.allocate::<u32>(256)?;
    let mut c_u32 = exec.allocate::<u32>(256)?;

    ops::math::vector_mul(&mut exec, &a_u32, &b_u32, &mut c_u32, 256)?;

    Ok(())
}

#[test]
fn test_math_vector_div_multi_types() -> Result<()> {
    let mut exec = Executor::new()?;

    let a = exec.allocate::<f32>(256)?;
    let b = exec.allocate::<f32>(256)?;
    let mut c = exec.allocate::<f32>(256)?;

    ops::math::vector_div(&mut exec, &a, &b, &mut c, 256)?;

    // Test with F64
    let a_f64 = exec.allocate::<f64>(256)?;
    let b_f64 = exec.allocate::<f64>(256)?;
    let mut c_f64 = exec.allocate::<f64>(256)?;

    ops::math::vector_div(&mut exec, &a_f64, &b_f64, &mut c_f64, 256)?;

    Ok(())
}

#[test]
fn test_math_min_max() -> Result<()> {
    let mut exec = Executor::new()?;

    // Test MIN
    let a = exec.allocate::<f32>(256)?;
    let b = exec.allocate::<f32>(256)?;
    let mut c = exec.allocate::<f32>(256)?;

    ops::math::min(&mut exec, &a, &b, &mut c, 256)?;

    // Test MAX with I32
    let a_i32 = exec.allocate::<i32>(256)?;
    let b_i32 = exec.allocate::<i32>(256)?;
    let mut c_i32 = exec.allocate::<i32>(256)?;

    ops::math::max(&mut exec, &a_i32, &b_i32, &mut c_i32, 256)?;

    Ok(())
}

#[test]
fn test_math_unary_operations() -> Result<()> {
    let mut exec = Executor::new()?;

    let a = exec.allocate::<f32>(256)?;
    let mut b = exec.allocate::<f32>(256)?;

    // Test ABS
    ops::math::abs(&mut exec, &a, &mut b, 256)?;

    // Test NEG
    ops::math::neg(&mut exec, &a, &mut b, 256)?;

    // Test RELU
    ops::math::relu(&mut exec, &a, &mut b, 256)?;

    // Test with I32
    let a_i32 = exec.allocate::<i32>(256)?;
    let mut b_i32 = exec.allocate::<i32>(256)?;

    ops::math::abs(&mut exec, &a_i32, &mut b_i32, 256)?;
    ops::math::neg(&mut exec, &a_i32, &mut b_i32, 256)?;

    Ok(())
}

#[test]
fn test_math_scalar_operations() -> Result<()> {
    ensure_kernels_loaded();
    let mut exec = Executor::new()?;

    // Test scalar_add with F32
    let a = exec.allocate::<f32>(256)?;
    let mut b = exec.allocate::<f32>(256)?;

    ops::math::scalar_add(&mut exec, &a, &mut b, 42.0f32, 256)?;

    // Test scalar_mul with I32
    let a_i32 = exec.allocate::<i32>(256)?;
    let mut b_i32 = exec.allocate::<i32>(256)?;

    ops::math::scalar_mul(&mut exec, &a_i32, &mut b_i32, 2i32, 256)?;

    Ok(())
}

#[test]
fn test_math_clip() -> Result<()> {
    let mut exec = Executor::new()?;

    // Test clip with F32
    let a = exec.allocate::<f32>(256)?;
    let mut b = exec.allocate::<f32>(256)?;

    ops::math::clip(&mut exec, &a, &mut b, -1.0f32, 1.0f32, 256)?;

    // Test clip with I32
    let a_i32 = exec.allocate::<i32>(256)?;
    let mut b_i32 = exec.allocate::<i32>(256)?;

    ops::math::clip(&mut exec, &a_i32, &mut b_i32, -100i32, 100i32, 256)?;

    Ok(())
}

// ============================================================================
// ops::reduce Integration Tests (Task 4.3 - All 3 operations)
// ============================================================================

#[test]
fn test_reduce_sum_multi_types() -> Result<()> {
    let mut exec = Executor::new()?;

    // Test with F32
    let input = exec.allocate::<f32>(1024)?;
    let mut output = exec.allocate::<f32>(3)?; // Needs at least 3 for temporaries

    ops::reduce::sum(&mut exec, &input, &mut output, 1024)?;

    // Test with I32
    let input_i32 = exec.allocate::<i32>(1024)?;
    let mut output_i32 = exec.allocate::<i32>(3)?; // Needs at least 3 for temporaries

    ops::reduce::sum(&mut exec, &input_i32, &mut output_i32, 1024)?;

    // Test with F64
    let input_f64 = exec.allocate::<f64>(1024)?;
    let mut output_f64 = exec.allocate::<f64>(3)?; // Needs at least 3 for temporaries

    ops::reduce::sum(&mut exec, &input_f64, &mut output_f64, 1024)?;

    Ok(())
}

#[test]
fn test_reduce_min_multi_types() -> Result<()> {
    let mut exec = Executor::new()?;

    // Test with F32
    let input = exec.allocate::<f32>(512)?;
    let mut output = exec.allocate::<f32>(3)?; // Needs at least 3 for temporaries

    ops::reduce::min(&mut exec, &input, &mut output, 512)?;

    // Test with I32
    let input_i32 = exec.allocate::<i32>(512)?;
    let mut output_i32 = exec.allocate::<i32>(3)?; // Needs at least 3 for temporaries

    ops::reduce::min(&mut exec, &input_i32, &mut output_i32, 512)?;

    Ok(())
}

#[test]
fn test_reduce_max_multi_types() -> Result<()> {
    let mut exec = Executor::new()?;

    // Test with F32
    let input = exec.allocate::<f32>(512)?;
    let mut output = exec.allocate::<f32>(3)?; // Needs at least 3 for temporaries

    ops::reduce::max(&mut exec, &input, &mut output, 512)?;

    // Test with U32
    let input_u32 = exec.allocate::<u32>(512)?;
    let mut output_u32 = exec.allocate::<u32>(3)?; // Needs at least 3 for temporaries

    ops::reduce::max(&mut exec, &input_u32, &mut output_u32, 512)?;

    Ok(())
}

// ============================================================================
// ops::activation Integration Tests (Task 4.3 - All 5 operations)
// ============================================================================

#[test]
fn test_activation_sigmoid_multi_types() -> Result<()> {
    let mut exec = Executor::new()?;

    // Test with F32
    let input = exec.allocate::<f32>(256)?;
    let mut output = exec.allocate::<f32>(256)?;

    ops::activation::sigmoid(&mut exec, &input, &mut output, 256)?;

    // Test with F64
    let input_f64 = exec.allocate::<f64>(256)?;
    let mut output_f64 = exec.allocate::<f64>(256)?;

    ops::activation::sigmoid(&mut exec, &input_f64, &mut output_f64, 256)?;

    Ok(())
}

#[test]
fn test_activation_tanh_multi_types() -> Result<()> {
    let mut exec = Executor::new()?;

    // Test with F32
    let input = exec.allocate::<f32>(256)?;
    let mut output = exec.allocate::<f32>(256)?;

    ops::activation::tanh(&mut exec, &input, &mut output, 256)?;

    // Test with F64
    let input_f64 = exec.allocate::<f64>(256)?;
    let mut output_f64 = exec.allocate::<f64>(256)?;

    ops::activation::tanh(&mut exec, &input_f64, &mut output_f64, 256)?;

    Ok(())
}

#[test]
fn test_activation_gelu() -> Result<()> {
    let mut exec = Executor::new()?;

    let input = exec.allocate::<f32>(256)?;
    let mut output = exec.allocate::<f32>(256)?;

    ops::activation::gelu(&mut exec, &input, &mut output, 256)?;

    // Test with F64
    let input_f64 = exec.allocate::<f64>(256)?;
    let mut output_f64 = exec.allocate::<f64>(256)?;

    ops::activation::gelu(&mut exec, &input_f64, &mut output_f64, 256)?;

    Ok(())
}

#[test]
fn test_activation_softmax() -> Result<()> {
    let mut exec = Executor::new()?;

    let input = exec.allocate::<f32>(256)?;
    let mut output = exec.allocate::<f32>(256)?;

    ops::activation::softmax(&mut exec, &input, &mut output, 256)?;

    // Test with F64
    let input_f64 = exec.allocate::<f64>(256)?;
    let mut output_f64 = exec.allocate::<f64>(256)?;

    ops::activation::softmax(&mut exec, &input_f64, &mut output_f64, 256)?;

    Ok(())
}

// ============================================================================
// ops::loss Integration Tests (Task 4.3 - All 3 operations)
// ============================================================================

#[test]
fn test_loss_mse_multi_types() -> Result<()> {
    let mut exec = Executor::new()?;

    // Test with F32
    let predictions = exec.allocate::<f32>(256)?;
    let targets = exec.allocate::<f32>(256)?;
    let mut loss = exec.allocate::<f32>(3)?; // Needs at least 3

    ops::loss::mse(&mut exec, &predictions, &targets, &mut loss, 256)?;

    // Test with F64
    let predictions_f64 = exec.allocate::<f64>(256)?;
    let targets_f64 = exec.allocate::<f64>(256)?;
    let mut loss_f64 = exec.allocate::<f64>(3)?; // Needs at least 3 for temporaries

    ops::loss::mse(&mut exec, &predictions_f64, &targets_f64, &mut loss_f64, 256)?;

    Ok(())
}

#[test]
fn test_loss_cross_entropy() -> Result<()> {
    let mut exec = Executor::new()?;

    let predictions = exec.allocate::<f32>(100)?;
    let targets = exec.allocate::<f32>(100)?;
    let mut loss = exec.allocate::<f32>(3)?; // Needs at least 3

    ops::loss::cross_entropy(&mut exec, &predictions, &targets, &mut loss, 100)?;

    // Test with F64
    let predictions_f64 = exec.allocate::<f64>(100)?;
    let targets_f64 = exec.allocate::<f64>(100)?;
    let mut loss_f64 = exec.allocate::<f64>(3)?; // Needs at least 3 for temporaries

    ops::loss::cross_entropy(&mut exec, &predictions_f64, &targets_f64, &mut loss_f64, 100)?;

    Ok(())
}

#[test]
fn test_loss_binary_cross_entropy() -> Result<()> {
    let mut exec = Executor::new()?;

    let predictions = exec.allocate::<f32>(100)?;
    let targets = exec.allocate::<f32>(100)?;
    let mut loss = exec.allocate::<f32>(3)?; // Needs at least 3

    ops::loss::binary_cross_entropy(&mut exec, &predictions, &targets, &mut loss, 100)?;

    // Test with F64
    let predictions_f64 = exec.allocate::<f64>(100)?;
    let targets_f64 = exec.allocate::<f64>(100)?;
    let mut loss_f64 = exec.allocate::<f64>(3)?; // Needs at least 3 for temporaries

    ops::loss::binary_cross_entropy(&mut exec, &predictions_f64, &targets_f64, &mut loss_f64, 100)?;

    Ok(())
}

// ============================================================================
// Large Buffer Tests (Task 4.3 - n > 10000)
// ============================================================================

#[test]
fn test_large_buffer_vector_add() -> Result<()> {
    ensure_kernels_loaded();
    let mut exec = Executor::new()?;

    // Large buffer: 20000 elements
    let a = exec.allocate::<f32>(20000)?;
    let b = exec.allocate::<f32>(20000)?;
    let mut c = exec.allocate::<f32>(20000)?;

    ops::math::vector_add(&mut exec, &a, &b, &mut c, 20000)?;

    Ok(())
}

#[test]
fn test_large_buffer_vector_mul() -> Result<()> {
    let mut exec = Executor::new()?;

    // Large buffer: 15000 elements
    let a = exec.allocate::<f32>(15000)?;
    let b = exec.allocate::<f32>(15000)?;
    let mut c = exec.allocate::<f32>(15000)?;

    ops::math::vector_mul(&mut exec, &a, &b, &mut c, 15000)?;

    Ok(())
}

#[test]
fn test_large_buffer_reduce_sum() -> Result<()> {
    let mut exec = Executor::new()?;

    // Large buffer: 30000 elements
    let input = exec.allocate::<f32>(30000)?;
    let mut output = exec.allocate::<f32>(3)?; // Needs at least 3 for temporaries

    ops::reduce::sum(&mut exec, &input, &mut output, 30000)?;

    Ok(())
}

#[test]
fn test_large_buffer_reduce_min() -> Result<()> {
    let mut exec = Executor::new()?;

    // Large buffer: 25000 elements
    let input = exec.allocate::<f32>(25000)?;
    let mut output = exec.allocate::<f32>(3)?; // Needs at least 3 for temporaries

    ops::reduce::min(&mut exec, &input, &mut output, 25000)?;

    Ok(())
}

#[test]
fn test_large_buffer_softmax() -> Result<()> {
    let mut exec = Executor::new()?;

    // Large buffer: 10000 elements
    let input = exec.allocate::<f32>(10000)?;
    let mut output = exec.allocate::<f32>(10000)?;

    ops::activation::softmax(&mut exec, &input, &mut output, 10000)?;

    Ok(())
}

// ============================================================================
// End-to-End Workflow Tests
// ============================================================================

#[test]
fn test_neural_network_layer_forward_pass() -> Result<()> {
    let mut exec = Executor::new()?;

    let n = 1024;

    // Input -> Linear transformation -> Activation
    let input = exec.allocate::<f32>(n)?;
    let mut linear_out = exec.allocate::<f32>(n)?;
    let mut activated = exec.allocate::<f32>(n)?;

    // Simulated linear layer (just multiplication for simplicity)
    let weights = exec.allocate::<f32>(n)?;
    ops::math::vector_mul(&mut exec, &input, &weights, &mut linear_out, n)?;

    // Apply activation
    ops::activation::sigmoid(&mut exec, &linear_out, &mut activated, n)?;

    Ok(())
}

#[test]
fn test_training_step_simulation() -> Result<()> {
    let mut exec = Executor::new()?;

    let n = 512;

    // Forward pass
    let predictions = exec.allocate::<f32>(n)?;
    let targets = exec.allocate::<f32>(n)?;

    // Compute loss
    let mut loss = exec.allocate::<f32>(3)?; // Needs at least 3
    ops::loss::mse(&mut exec, &predictions, &targets, &mut loss, n)?;

    // Backward pass would go here (simulated with basic operations)
    let mut gradients = exec.allocate::<f32>(n)?;
    ops::math::vector_sub(&mut exec, &predictions, &targets, &mut gradients, n)?;

    Ok(())
}

#[test]
fn test_multi_layer_forward_pass() -> Result<()> {
    let mut exec = Executor::new()?;

    let n = 256;

    // Layer 1: Input -> Hidden
    let input = exec.allocate::<f32>(n)?;
    let mut hidden1 = exec.allocate::<f32>(n)?;
    let mut activated1 = exec.allocate::<f32>(n)?;

    ops::math::scalar_mul(&mut exec, &input, &mut hidden1, 0.5f32, n)?;
    ops::math::relu(&mut exec, &hidden1, &mut activated1, n)?;

    // Layer 2: Hidden -> Output
    let mut hidden2 = exec.allocate::<f32>(n)?;
    let mut output = exec.allocate::<f32>(n)?;

    ops::math::scalar_mul(&mut exec, &activated1, &mut hidden2, 0.5f32, n)?;
    ops::activation::sigmoid(&mut exec, &hidden2, &mut output, n)?;

    Ok(())
}
