//! Integration test for kernel execution in hologram-core

use hologram_core::kernel::vector_add_kernel;
use hologram_core::{Buffer, Executor};
use hologram_codegen::register_all_kernels_from_directory;

#[test]
fn test_vector_add_with_kernel() {
    // Load kernels
    let _ = register_all_kernels_from_directory("../../target/kernel-libs");
    
    // Create executor
    let mut exec = Executor::new().unwrap();
    
    // Allocate buffers
    let mut a = exec.allocate::<f32>(3).unwrap();
    let mut b = exec.allocate::<f32>(3).unwrap();
    let mut c = exec.allocate::<f32>(3).unwrap();
    
    // Copy test data
    let data_a = vec![1.0f32, 2.0, 3.0];
    let data_b = vec![4.0f32, 5.0, 6.0];
    
    a.copy_from_slice(&mut exec, &data_a).unwrap();
    b.copy_from_slice(&mut exec, &data_b).unwrap();
    
    // Execute kernel
    vector_add_kernel(&mut exec, &a, &b, &mut c, 3).unwrap();
    
    // Read results
    let result = c.to_vec(&exec).unwrap();
    
    assert_eq!(result, vec![5.0, 7.0, 9.0]);
    println!("✅ Kernel integration test passed: {:?}", result);
}

