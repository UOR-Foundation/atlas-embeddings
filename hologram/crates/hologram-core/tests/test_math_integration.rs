//! Integration tests for generator-based math operations
//!
//! These tests verify that the new math_v2 module (Phase 3) works correctly
//! with real buffers and data.

use hologram_core::{ops::math, Executor};

#[test]
fn test_vector_add_v2_f32() -> hologram_core::Result<()> {
    let mut exec = Executor::new()?;

    // Allocate boundary buffers (map to class_bases[96])
    // Each boundary buffer holds 48×256 = 12,288 bytes = 3,072 f32 elements
    // Use consecutive classes (0, 1, 2) for better neighbor likelihood
    let mut a = exec.allocate_boundary::<f32>(0, 48, 256)?;
    let mut b = exec.allocate_boundary::<f32>(2, 48, 256)?;
    let mut c = exec.allocate_boundary::<f32>(1, 48, 256)?;

    // Prepare test data (boundary buffers hold 12,288 bytes = 3,072 f32 elements)
    let data_a: Vec<f32> = (0..3072).map(|i| i as f32).collect();
    let data_b: Vec<f32> = (0..3072).map(|i| (i as f32) * 2.0).collect();

    // Copy data to buffers
    a.copy_from_slice(&mut exec, &data_a)?;
    b.copy_from_slice(&mut exec, &data_b)?;

    // Execute vector_add using generators (test with 2048 elements)
    math::vector_add(&mut exec, &a, &b, &mut c, 2048)?;

    // Read results
    let result = c.to_vec(&exec)?;

    // Verify a few values
    assert!((result[0] - 0.0).abs() < 0.001); // 0 + 0 = 0
    assert!((result[1] - 3.0).abs() < 0.001); // 1 + 2 = 3
    assert!((result[10] - 30.0).abs() < 0.001); // 10 + 20 = 30
    assert!((result[100] - 300.0).abs() < 0.001); // 100 + 200 = 300

    Ok(())
}

#[test]
fn test_vector_sub_v2_f32() -> hologram_core::Result<()> {
    let mut exec = Executor::new()?;

    // Allocate boundary buffers (map to class_bases[96])
    // Use consecutive classes (3, 4, 5) where a → c needs to be neighbors for split
    let mut a = exec.allocate_boundary::<f32>(3, 48, 256)?;
    let mut b = exec.allocate_boundary::<f32>(5, 48, 256)?;
    let mut c = exec.allocate_boundary::<f32>(4, 48, 256)?;

    // Prepare test data (boundary buffers hold 12,288 bytes = 3,072 f32 elements)
    let data_a: Vec<f32> = (0..3072).map(|i| (i as f32) * 10.0).collect();
    let data_b: Vec<f32> = (0..3072).map(|i| i as f32).collect();

    // Copy data to buffers
    a.copy_from_slice(&mut exec, &data_a)?;
    b.copy_from_slice(&mut exec, &data_b)?;

    // Execute vector_sub using generators (test with 1024 elements)
    math::vector_sub(&mut exec, &a, &b, &mut c, 1024)?;

    // Read results
    let result = c.to_vec(&exec)?;

    // Verify a few values
    assert!((result[0] - 0.0).abs() < 0.001); // 0 - 0 = 0
    assert!((result[1] - 9.0).abs() < 0.001); // 10 - 1 = 9
    assert!((result[10] - 90.0).abs() < 0.001); // 100 - 10 = 90

    Ok(())
}

#[test]
fn test_vector_mul_v2_f32() -> hologram_core::Result<()> {
    let mut exec = Executor::new()?;

    // Allocate boundary buffers (map to class_bases[96])
    // Use consecutive classes (6, 7, 8) where a → c needs to be neighbors for merge
    let mut a = exec.allocate_boundary::<f32>(6, 48, 256)?;
    let mut b = exec.allocate_boundary::<f32>(8, 48, 256)?;
    let mut c = exec.allocate_boundary::<f32>(7, 48, 256)?;

    // Prepare test data (boundary buffers hold 12,288 bytes = 3,072 f32 elements)
    let data_a: Vec<f32> = (0..3072).map(|i| (i as f32) + 1.0).collect();
    let data_b: Vec<f32> = (0..3072).map(|_i| 2.0).collect();

    // Copy data to buffers
    a.copy_from_slice(&mut exec, &data_a)?;
    b.copy_from_slice(&mut exec, &data_b)?;

    // Execute vector_mul using generators (test with 512 elements)
    math::vector_mul(&mut exec, &a, &b, &mut c, 512)?;

    // Read results
    let result = c.to_vec(&exec)?;

    // Verify a few values
    assert!((result[0] - 2.0).abs() < 0.001); // 1 * 2 = 2
    assert!((result[1] - 4.0).abs() < 0.001); // 2 * 2 = 4
    assert!((result[10] - 22.0).abs() < 0.001); // 11 * 2 = 22

    Ok(())
}

#[test]
fn test_vector_operations_v2_chained() -> hologram_core::Result<()> {
    let mut exec = Executor::new()?;

    // Test chaining operations: (a + b) - c using boundary buffers
    // Need: a → temp neighbors (for merge), temp → result neighbors (for split)
    let mut a = exec.allocate_boundary::<f32>(9, 48, 256)?;
    let mut b = exec.allocate_boundary::<f32>(12, 48, 256)?;
    let mut c = exec.allocate_boundary::<f32>(13, 48, 256)?;
    let mut temp = exec.allocate_boundary::<f32>(10, 48, 256)?;
    let mut result = exec.allocate_boundary::<f32>(11, 48, 256)?;

    // Prepare test data (boundary buffers hold 12,288 bytes = 3,072 f32 elements)
    let data_a: Vec<f32> = (0..3072).map(|i| i as f32 * 3.0).collect();
    let data_b: Vec<f32> = (0..3072).map(|i| i as f32 * 2.0).collect();
    let data_c: Vec<f32> = (0..3072).map(|i| i as f32).collect();

    a.copy_from_slice(&mut exec, &data_a)?;
    b.copy_from_slice(&mut exec, &data_b)?;
    c.copy_from_slice(&mut exec, &data_c)?;

    // Chain operations (test with 256 elements)
    math::vector_add(&mut exec, &a, &b, &mut temp, 256)?; // temp = a + b
    math::vector_sub(&mut exec, &temp, &c, &mut result, 256)?; // result = temp - c

    // Read results
    let res = result.to_vec(&exec)?;

    // Verify: (i*3 + i*2) - i = i*5 - i = i*4
    assert!((res[0] - 0.0).abs() < 0.001); // 0*4 = 0
    assert!((res[1] - 4.0).abs() < 0.001); // 1*4 = 4
    assert!((res[10] - 40.0).abs() < 0.001); // 10*4 = 40

    Ok(())
}
