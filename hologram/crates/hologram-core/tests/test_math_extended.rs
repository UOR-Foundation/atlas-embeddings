//! Extended integration tests for generator-based math operations (Phase 3)
//!
//! Tests the new operations: div, min, max, abs, neg, relu

use hologram_core::{ops::math, Executor};

#[test]
fn test_vector_div_v2_f32() -> hologram_core::Result<()> {
    let mut exec = Executor::new()?;

    // Use known-working class assignments
    let mut a = exec.allocate_boundary::<f32>(0, 48, 256)?;
    let mut b = exec.allocate_boundary::<f32>(2, 48, 256)?;
    let mut c = exec.allocate_boundary::<f32>(1, 48, 256)?;

    // Prepare test data (12,288 bytes = 3,072 f32 elements)
    let data_a: Vec<f32> = (0..3072).map(|i| (i as f32 + 1.0) * 10.0).collect();
    let data_b: Vec<f32> = (0..3072).map(|i| (i as f32 + 1.0) * 2.0).collect();

    a.copy_from_slice(&mut exec, &data_a)?;
    b.copy_from_slice(&mut exec, &data_b)?;

    // Execute vector_div using generators (1024 elements)
    math::vector_div(&mut exec, &a, &b, &mut c, 1024)?;

    // Read results
    let result = c.to_vec(&exec)?;

    // Verify a few values: (i+1)*10 / (i+1)*2 = 5.0
    assert!((result[0] - 5.0).abs() < 0.001); // 10 / 2 = 5
    assert!((result[1] - 5.0).abs() < 0.001); // 20 / 4 = 5
    assert!((result[10] - 5.0).abs() < 0.001); // 110 / 22 = 5

    Ok(())
}

#[test]
fn test_min_v2_f32() -> hologram_core::Result<()> {
    let mut exec = Executor::new()?;

    // Use known-working class assignments
    let mut a = exec.allocate_boundary::<f32>(3, 48, 256)?;
    let mut b = exec.allocate_boundary::<f32>(5, 48, 256)?;
    let mut c = exec.allocate_boundary::<f32>(4, 48, 256)?;

    // Prepare test data where a and b alternate being smaller
    let data_a: Vec<f32> = (0..3072)
        .map(|i| if i % 2 == 0 { i as f32 } else { i as f32 + 10.0 })
        .collect();
    let data_b: Vec<f32> = (0..3072)
        .map(|i| if i % 2 == 0 { i as f32 + 10.0 } else { i as f32 })
        .collect();

    a.copy_from_slice(&mut exec, &data_a)?;
    b.copy_from_slice(&mut exec, &data_b)?;

    // Execute min using generators
    math::min(&mut exec, &a, &b, &mut c, 1024)?;

    // Read results
    let result = c.to_vec(&exec)?;

    // Verify: should always pick the smaller value (which is i for all elements)
    assert!((result[0] - 0.0).abs() < 0.001); // min(0, 10) = 0
    assert!((result[1] - 1.0).abs() < 0.001); // min(11, 1) = 1
    assert!((result[10] - 10.0).abs() < 0.001); // min(10, 20) = 10
    assert!((result[11] - 11.0).abs() < 0.001); // min(21, 11) = 11

    Ok(())
}

#[test]
fn test_max_v2_f32() -> hologram_core::Result<()> {
    let mut exec = Executor::new()?;

    // Use known-working class assignments
    let mut a = exec.allocate_boundary::<f32>(6, 48, 256)?;
    let mut b = exec.allocate_boundary::<f32>(8, 48, 256)?;
    let mut c = exec.allocate_boundary::<f32>(7, 48, 256)?;

    // Prepare test data where a and b alternate being larger
    let data_a: Vec<f32> = (0..3072)
        .map(|i| if i % 2 == 0 { i as f32 + 10.0 } else { i as f32 })
        .collect();
    let data_b: Vec<f32> = (0..3072)
        .map(|i| if i % 2 == 0 { i as f32 } else { i as f32 + 10.0 })
        .collect();

    a.copy_from_slice(&mut exec, &data_a)?;
    b.copy_from_slice(&mut exec, &data_b)?;

    // Execute max using generators
    math::max(&mut exec, &a, &b, &mut c, 1024)?;

    // Read results
    let result = c.to_vec(&exec)?;

    // Verify: should always pick the larger value (which is i + 10 for all elements)
    assert!((result[0] - 10.0).abs() < 0.001); // max(10, 0) = 10
    assert!((result[1] - 11.0).abs() < 0.001); // max(1, 11) = 11
    assert!((result[10] - 20.0).abs() < 0.001); // max(20, 10) = 20
    assert!((result[11] - 21.0).abs() < 0.001); // max(11, 21) = 21

    Ok(())
}

#[test]
fn test_abs_v2_f32() -> hologram_core::Result<()> {
    let mut exec = Executor::new()?;

    // Use known-working class pair (0→1)
    let mut a = exec.allocate_boundary::<f32>(0, 48, 256)?;
    let mut b = exec.allocate_boundary::<f32>(1, 48, 256)?;

    // Prepare test data with negative and positive values
    let data_a: Vec<f32> = (0..3072)
        .map(|i| if i % 2 == 0 { -(i as f32) } else { i as f32 })
        .collect();

    a.copy_from_slice(&mut exec, &data_a)?;

    // Execute abs using generators
    math::abs(&mut exec, &a, &mut b, 1024)?;

    // Read results
    let result = b.to_vec(&exec)?;

    // Verify: all values should be positive
    assert!((result[0] - 0.0).abs() < 0.001); // abs(-0) = 0
    assert!((result[1] - 1.0).abs() < 0.001); // abs(1) = 1
    assert!((result[2] - 2.0).abs() < 0.001); // abs(-2) = 2
    assert!((result[10] - 10.0).abs() < 0.001); // abs(-10) = 10
    assert!((result[11] - 11.0).abs() < 0.001); // abs(11) = 11

    Ok(())
}

#[test]
fn test_neg_v2_f32() -> hologram_core::Result<()> {
    let mut exec = Executor::new()?;

    // Use known-working class pair (3→4)
    let mut a = exec.allocate_boundary::<f32>(3, 48, 256)?;
    let mut b = exec.allocate_boundary::<f32>(4, 48, 256)?;

    // Prepare test data
    let data_a: Vec<f32> = (0..3072).map(|i| i as f32 * 2.0).collect();

    a.copy_from_slice(&mut exec, &data_a)?;

    // Execute neg using generators
    math::neg(&mut exec, &a, &mut b, 1024)?;

    // Read results
    let result = b.to_vec(&exec)?;

    // Verify: all values should be negated
    assert!((result[0] - 0.0).abs() < 0.001); // -0 = 0
    assert!((result[1] - (-2.0)).abs() < 0.001); // -(2) = -2
    assert!((result[10] - (-20.0)).abs() < 0.001); // -(20) = -20
    assert!((result[100] - (-200.0)).abs() < 0.001); // -(200) = -200

    Ok(())
}

#[test]
fn test_relu_v2_f32() -> hologram_core::Result<()> {
    let mut exec = Executor::new()?;

    // Use known-working class pair (6→7)
    let mut a = exec.allocate_boundary::<f32>(6, 48, 256)?;
    let mut b = exec.allocate_boundary::<f32>(7, 48, 256)?;

    // Prepare test data with negative and positive values
    let data_a: Vec<f32> = (0..3072)
        .map(|i| {
            // Create pattern: -2, -1, 0, 1, 2, -2, -1, 0, 1, 2, ...
            (i % 5) as f32 - 2.0
        })
        .collect();

    a.copy_from_slice(&mut exec, &data_a)?;

    // Execute relu using generators
    math::relu(&mut exec, &a, &mut b, 1024)?;

    // Read results
    let result = b.to_vec(&exec)?;

    // Verify: negative values should be 0, positive values preserved
    assert!((result[0] - 0.0).abs() < 0.001); // relu(-2) = 0
    assert!((result[1] - 0.0).abs() < 0.001); // relu(-1) = 0
    assert!((result[2] - 0.0).abs() < 0.001); // relu(0) = 0
    assert!((result[3] - 1.0).abs() < 0.001); // relu(1) = 1
    assert!((result[4] - 2.0).abs() < 0.001); // relu(2) = 2
    assert!((result[5] - 0.0).abs() < 0.001); // relu(-2) = 0
    assert!((result[8] - 1.0).abs() < 0.001); // relu(1) = 1

    Ok(())
}

#[test]
fn test_chained_operations_v2() -> hologram_core::Result<()> {
    let mut exec = Executor::new()?;

    // Test chain: (a * b) / c using known-working class assignments
    // Reuse exact same structure as basic chained test which works
    let mut a = exec.allocate_boundary::<f32>(9, 48, 256)?;
    let mut b = exec.allocate_boundary::<f32>(12, 48, 256)?;
    let mut c = exec.allocate_boundary::<f32>(13, 48, 256)?;
    let mut temp = exec.allocate_boundary::<f32>(10, 48, 256)?; // a * b (9→10)
    let mut result = exec.allocate_boundary::<f32>(11, 48, 256)?; // temp / c (10→11)

    // Prepare test data
    let data_a: Vec<f32> = (0..3072).map(|i| (i as f32 + 1.0) * 2.0).collect(); // 2, 4, 6, 8, ...
    let data_b: Vec<f32> = (0..3072).map(|i| (i as f32 + 1.0) * 3.0).collect(); // 3, 6, 9, 12, ...
    let data_c: Vec<f32> = (0..3072).map(|i| (i as f32 + 1.0) * 2.0).collect(); // 2, 4, 6, 8, ...

    a.copy_from_slice(&mut exec, &data_a)?;
    b.copy_from_slice(&mut exec, &data_b)?;
    c.copy_from_slice(&mut exec, &data_c)?;

    // Execute chain: temp = a * b, result = temp / c
    // a * b = 2(i+1) * 3(i+1) = 6(i+1)²
    // result = 6(i+1)² / 2(i+1) = 3(i+1)
    math::vector_mul(&mut exec, &a, &b, &mut temp, 256)?;
    math::vector_div(&mut exec, &temp, &c, &mut result, 256)?;

    // Read results
    let res = result.to_vec(&exec)?;

    // Verify: result should be 3(i+1)
    assert!((res[0] - 3.0).abs() < 0.001); // 3*(0+1) = 3
    assert!((res[1] - 6.0).abs() < 0.001); // 3*(1+1) = 6
    assert!((res[10] - 33.0).abs() < 0.001); // 3*(10+1) = 33

    Ok(())
}
