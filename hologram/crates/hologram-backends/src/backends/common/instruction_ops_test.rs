//! Tests for shared instruction implementations
//!
//! Tests all instruction operations in the instruction_ops module to ensure
//! correct behavior across different backends.

#[cfg(test)]
mod tests {
    use super::super::instruction_ops::*;
    use crate::backend::{BlockDim, ExecutionContext, GridDim};
    use crate::backends::common::ExecutionState;
    use crate::backends::cpu::memory::MemoryManager as CpuMemoryManager;
    use crate::isa::{Condition, Predicate, Register, Type};
    use parking_lot::RwLock;
    use std::collections::HashMap;
    use std::sync::Arc;

    /// Helper function to create a test execution state
    fn create_test_state() -> ExecutionState<CpuMemoryManager> {
        let memory = Arc::new(RwLock::new(CpuMemoryManager::new()));
        let context = ExecutionContext::new(
            (0, 0, 0),
            (0, 0, 0),
            GridDim { x: 1, y: 1, z: 1 },
            BlockDim { x: 1, y: 1, z: 1 },
        );
        let labels = HashMap::new();
        ExecutionState::new(1, memory, context, labels)
    }

    // ================================================================================================
    // Data Movement Instructions
    // ================================================================================================

    #[test]
    fn test_mov_i32() {
        let mut state = create_test_state();

        // Setup: Write value to source register
        state.current_lane_mut().registers.write_i32(Register(1), 42).unwrap();

        // Execute MOV
        execute_mov(&mut state, Type::I32, Register(2), Register(1)).unwrap();

        // Verify: Destination register contains copied value
        let result = state.current_lane().registers.read_i32(Register(2)).unwrap();
        assert_eq!(result, 42);
    }

    #[test]
    fn test_mov_f32() {
        let mut state = create_test_state();

        state
            .current_lane_mut()
            .registers
            .write_f32(Register(1), std::f32::consts::PI)
            .unwrap();
        execute_mov(&mut state, Type::F32, Register(2), Register(1)).unwrap();

        let result = state.current_lane().registers.read_f32(Register(2)).unwrap();
        assert_eq!(result, std::f32::consts::PI);
    }

    #[test]
    fn test_cvt_i32_to_f32() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_i32(Register(1), 100).unwrap();
        execute_cvt(&mut state, Type::I32, Type::F32, Register(2), Register(1)).unwrap();

        let result = state.current_lane().registers.read_f32(Register(2)).unwrap();
        assert_eq!(result, 100.0);
    }

    #[test]
    fn test_cvt_f32_to_i32() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_f32(Register(1), 99.7).unwrap();
        execute_cvt(&mut state, Type::F32, Type::I32, Register(2), Register(1)).unwrap();

        let result = state.current_lane().registers.read_i32(Register(2)).unwrap();
        assert_eq!(result, 99);
    }

    // ================================================================================================
    // Arithmetic Instructions
    // ================================================================================================

    #[test]
    fn test_add_i32() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_i32(Register(1), 10).unwrap();
        state.current_lane_mut().registers.write_i32(Register(2), 20).unwrap();

        execute_add(&mut state, Type::I32, Register(3), Register(1), Register(2)).unwrap();

        let result = state.current_lane().registers.read_i32(Register(3)).unwrap();
        assert_eq!(result, 30);
    }

    #[test]
    fn test_add_f32() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_f32(Register(1), 1.5).unwrap();
        state.current_lane_mut().registers.write_f32(Register(2), 2.5).unwrap();

        execute_add(&mut state, Type::F32, Register(3), Register(1), Register(2)).unwrap();

        let result = state.current_lane().registers.read_f32(Register(3)).unwrap();
        assert_eq!(result, 4.0);
    }

    #[test]
    fn test_add_wrapping() {
        let mut state = create_test_state();

        // Test wrapping addition for u8
        state.current_lane_mut().registers.write_u8(Register(1), 250).unwrap();
        state.current_lane_mut().registers.write_u8(Register(2), 10).unwrap();

        execute_add(&mut state, Type::U8, Register(3), Register(1), Register(2)).unwrap();

        let result = state.current_lane().registers.read_u8(Register(3)).unwrap();
        assert_eq!(result, 4); // 250 + 10 = 260 % 256 = 4
    }

    #[test]
    fn test_sub_i32() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_i32(Register(1), 30).unwrap();
        state.current_lane_mut().registers.write_i32(Register(2), 10).unwrap();

        execute_sub(&mut state, Type::I32, Register(3), Register(1), Register(2)).unwrap();

        let result = state.current_lane().registers.read_i32(Register(3)).unwrap();
        assert_eq!(result, 20);
    }

    #[test]
    fn test_mul_i32() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_i32(Register(1), 5).unwrap();
        state.current_lane_mut().registers.write_i32(Register(2), 7).unwrap();

        execute_mul(&mut state, Type::I32, Register(3), Register(1), Register(2)).unwrap();

        let result = state.current_lane().registers.read_i32(Register(3)).unwrap();
        assert_eq!(result, 35);
    }

    #[test]
    fn test_div_i32() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_i32(Register(1), 42).unwrap();
        state.current_lane_mut().registers.write_i32(Register(2), 6).unwrap();

        execute_div(&mut state, Type::I32, Register(3), Register(1), Register(2)).unwrap();

        let result = state.current_lane().registers.read_i32(Register(3)).unwrap();
        assert_eq!(result, 7);
    }

    #[test]
    fn test_mad_f32() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_f32(Register(1), 2.0).unwrap();
        state.current_lane_mut().registers.write_f32(Register(2), 3.0).unwrap();
        state.current_lane_mut().registers.write_f32(Register(3), 5.0).unwrap();

        // MAD: dst = a * b + c
        execute_mad(
            &mut state,
            Type::F32,
            Register(4),
            Register(1),
            Register(2),
            Register(3),
        )
        .unwrap();

        let result = state.current_lane().registers.read_f32(Register(4)).unwrap();
        assert_eq!(result, 11.0); // 2 * 3 + 5 = 11
    }

    #[test]
    fn test_fma_f32() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_f32(Register(1), 2.0).unwrap();
        state.current_lane_mut().registers.write_f32(Register(2), 3.0).unwrap();
        state.current_lane_mut().registers.write_f32(Register(3), 5.0).unwrap();

        // FMA: dst = a * b + c (fused)
        execute_fma(
            &mut state,
            Type::F32,
            Register(4),
            Register(1),
            Register(2),
            Register(3),
        )
        .unwrap();

        let result = state.current_lane().registers.read_f32(Register(4)).unwrap();
        assert_eq!(result, 11.0);
    }

    #[test]
    fn test_min_i32() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_i32(Register(1), 10).unwrap();
        state.current_lane_mut().registers.write_i32(Register(2), 20).unwrap();

        execute_min(&mut state, Type::I32, Register(3), Register(1), Register(2)).unwrap();

        let result = state.current_lane().registers.read_i32(Register(3)).unwrap();
        assert_eq!(result, 10);
    }

    #[test]
    fn test_max_i32() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_i32(Register(1), 10).unwrap();
        state.current_lane_mut().registers.write_i32(Register(2), 20).unwrap();

        execute_max(&mut state, Type::I32, Register(3), Register(1), Register(2)).unwrap();

        let result = state.current_lane().registers.read_i32(Register(3)).unwrap();
        assert_eq!(result, 20);
    }

    #[test]
    fn test_abs_i32() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_i32(Register(1), -42).unwrap();
        execute_abs(&mut state, Type::I32, Register(2), Register(1)).unwrap();

        let result = state.current_lane().registers.read_i32(Register(2)).unwrap();
        assert_eq!(result, 42);
    }

    #[test]
    fn test_neg_i32() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_i32(Register(1), 42).unwrap();
        execute_neg(&mut state, Type::I32, Register(2), Register(1)).unwrap();

        let result = state.current_lane().registers.read_i32(Register(2)).unwrap();
        assert_eq!(result, -42);
    }

    // ================================================================================================
    // Bitwise Instructions
    // ================================================================================================

    #[test]
    fn test_and_u32() {
        let mut state = create_test_state();

        state
            .current_lane_mut()
            .registers
            .write_u32(Register(1), 0xFF00)
            .unwrap();
        state
            .current_lane_mut()
            .registers
            .write_u32(Register(2), 0x0FFF)
            .unwrap();

        execute_and(&mut state, Type::U32, Register(3), Register(1), Register(2)).unwrap();

        let result = state.current_lane().registers.read_u32(Register(3)).unwrap();
        assert_eq!(result, 0x0F00);
    }

    #[test]
    fn test_or_u32() {
        let mut state = create_test_state();

        state
            .current_lane_mut()
            .registers
            .write_u32(Register(1), 0xFF00)
            .unwrap();
        state
            .current_lane_mut()
            .registers
            .write_u32(Register(2), 0x0FFF)
            .unwrap();

        execute_or(&mut state, Type::U32, Register(3), Register(1), Register(2)).unwrap();

        let result = state.current_lane().registers.read_u32(Register(3)).unwrap();
        assert_eq!(result, 0xFFFF);
    }

    #[test]
    fn test_xor_u32() {
        let mut state = create_test_state();

        state
            .current_lane_mut()
            .registers
            .write_u32(Register(1), 0xFF00)
            .unwrap();
        state
            .current_lane_mut()
            .registers
            .write_u32(Register(2), 0x0FFF)
            .unwrap();

        execute_xor(&mut state, Type::U32, Register(3), Register(1), Register(2)).unwrap();

        let result = state.current_lane().registers.read_u32(Register(3)).unwrap();
        assert_eq!(result, 0xF0FF);
    }

    #[test]
    fn test_not_u32() {
        let mut state = create_test_state();

        state
            .current_lane_mut()
            .registers
            .write_u32(Register(1), 0x0000FFFF)
            .unwrap();
        execute_not(&mut state, Type::U32, Register(2), Register(1)).unwrap();

        let result = state.current_lane().registers.read_u32(Register(2)).unwrap();
        assert_eq!(result, 0xFFFF0000);
    }

    #[test]
    fn test_shl_u32() {
        let mut state = create_test_state();

        state
            .current_lane_mut()
            .registers
            .write_u32(Register(1), 0x0001)
            .unwrap();
        state.current_lane_mut().registers.write_u32(Register(2), 4).unwrap();

        execute_shl(&mut state, Type::U32, Register(3), Register(1), Register(2)).unwrap();

        let result = state.current_lane().registers.read_u32(Register(3)).unwrap();
        assert_eq!(result, 0x0010);
    }

    #[test]
    fn test_shr_u32() {
        let mut state = create_test_state();

        state
            .current_lane_mut()
            .registers
            .write_u32(Register(1), 0x0010)
            .unwrap();
        state.current_lane_mut().registers.write_u32(Register(2), 4).unwrap();

        execute_shr(&mut state, Type::U32, Register(3), Register(1), Register(2)).unwrap();

        let result = state.current_lane().registers.read_u32(Register(3)).unwrap();
        assert_eq!(result, 0x0001);
    }

    // ================================================================================================
    // Comparison Instructions
    // ================================================================================================

    #[test]
    fn test_setcc_eq_true() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_i32(Register(1), 42).unwrap();
        state.current_lane_mut().registers.write_i32(Register(2), 42).unwrap();

        execute_setcc(
            &mut state,
            Condition::EQ,
            Type::I32,
            Predicate(0),
            Register(1),
            Register(2),
        )
        .unwrap();

        let result = state.current_lane().registers.read_predicate(Predicate(0)).unwrap();
        assert_eq!(result, true);
    }

    #[test]
    fn test_setcc_eq_false() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_i32(Register(1), 42).unwrap();
        state.current_lane_mut().registers.write_i32(Register(2), 43).unwrap();

        execute_setcc(
            &mut state,
            Condition::EQ,
            Type::I32,
            Predicate(0),
            Register(1),
            Register(2),
        )
        .unwrap();

        let result = state.current_lane().registers.read_predicate(Predicate(0)).unwrap();
        assert_eq!(result, false);
    }

    #[test]
    fn test_setcc_lt() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_i32(Register(1), 10).unwrap();
        state.current_lane_mut().registers.write_i32(Register(2), 20).unwrap();

        execute_setcc(
            &mut state,
            Condition::LT,
            Type::I32,
            Predicate(0),
            Register(1),
            Register(2),
        )
        .unwrap();

        let result = state.current_lane().registers.read_predicate(Predicate(0)).unwrap();
        assert_eq!(result, true);
    }

    #[test]
    fn test_setcc_gt() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_i32(Register(1), 20).unwrap();
        state.current_lane_mut().registers.write_i32(Register(2), 10).unwrap();

        execute_setcc(
            &mut state,
            Condition::GT,
            Type::I32,
            Predicate(0),
            Register(1),
            Register(2),
        )
        .unwrap();

        let result = state.current_lane().registers.read_predicate(Predicate(0)).unwrap();
        assert_eq!(result, true);
    }

    // ================================================================================================
    // Math Functions
    // ================================================================================================

    #[test]
    fn test_sin_f32() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_f32(Register(1), 0.0).unwrap();
        execute_sin(&mut state, Type::F32, Register(2), Register(1)).unwrap();

        let result = state.current_lane().registers.read_f32(Register(2)).unwrap();
        assert!((result - 0.0).abs() < 1e-6);
    }

    #[test]
    fn test_cos_f32() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_f32(Register(1), 0.0).unwrap();
        execute_cos(&mut state, Type::F32, Register(2), Register(1)).unwrap();

        let result = state.current_lane().registers.read_f32(Register(2)).unwrap();
        assert!((result - 1.0).abs() < 1e-6);
    }

    #[test]
    fn test_exp_f32() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_f32(Register(1), 0.0).unwrap();
        execute_exp(&mut state, Type::F32, Register(2), Register(1)).unwrap();

        let result = state.current_lane().registers.read_f32(Register(2)).unwrap();
        assert!((result - 1.0).abs() < 1e-6);
    }

    #[test]
    fn test_log_f32() {
        let mut state = create_test_state();

        state
            .current_lane_mut()
            .registers
            .write_f32(Register(1), std::f32::consts::E)
            .unwrap();
        execute_log(&mut state, Type::F32, Register(2), Register(1)).unwrap();

        let result = state.current_lane().registers.read_f32(Register(2)).unwrap();
        assert!((result - 1.0).abs() < 1e-6);
    }

    #[test]
    fn test_sqrt_f32() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_f32(Register(1), 16.0).unwrap();
        execute_sqrt(&mut state, Type::F32, Register(2), Register(1)).unwrap();

        let result = state.current_lane().registers.read_f32(Register(2)).unwrap();
        assert_eq!(result, 4.0);
    }

    #[test]
    fn test_sigmoid_f32() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_f32(Register(1), 0.0).unwrap();
        execute_sigmoid(&mut state, Type::F32, Register(2), Register(1)).unwrap();

        let result = state.current_lane().registers.read_f32(Register(2)).unwrap();
        assert!((result - 0.5).abs() < 1e-6);
    }

    #[test]
    fn test_tanh_f32() {
        let mut state = create_test_state();

        state.current_lane_mut().registers.write_f32(Register(1), 0.0).unwrap();
        execute_tanh(&mut state, Type::F32, Register(2), Register(1)).unwrap();

        let result = state.current_lane().registers.read_f32(Register(2)).unwrap();
        assert!((result - 0.0).abs() < 1e-6);
    }

    // ================================================================================================
    // Selection Instruction
    // ================================================================================================

    #[test]
    fn test_sel_true() {
        let mut state = create_test_state();

        state
            .current_lane_mut()
            .registers
            .write_predicate(Predicate(0), true)
            .unwrap();
        state.current_lane_mut().registers.write_i32(Register(1), 42).unwrap();
        state.current_lane_mut().registers.write_i32(Register(2), 99).unwrap();

        execute_sel(
            &mut state,
            Type::I32,
            Register(3),
            Predicate(0),
            Register(1),
            Register(2),
        )
        .unwrap();

        let result = state.current_lane().registers.read_i32(Register(3)).unwrap();
        assert_eq!(result, 42);
    }

    #[test]
    fn test_sel_false() {
        let mut state = create_test_state();

        state
            .current_lane_mut()
            .registers
            .write_predicate(Predicate(0), false)
            .unwrap();
        state.current_lane_mut().registers.write_i32(Register(1), 42).unwrap();
        state.current_lane_mut().registers.write_i32(Register(2), 99).unwrap();

        execute_sel(
            &mut state,
            Type::I32,
            Register(3),
            Predicate(0),
            Register(1),
            Register(2),
        )
        .unwrap();

        let result = state.current_lane().registers.read_i32(Register(3)).unwrap();
        assert_eq!(result, 99);
    }

    // ================================================================================================
    // Reduction Instructions
    // ================================================================================================

    #[test]
    fn test_reduce_add_i32() {
        let mut state = create_test_state();

        // Setup: registers 1-5 contain values to sum
        for i in 0..5 {
            state
                .current_lane_mut()
                .registers
                .write_i32(Register(i + 1), (i + 1) as i32)
                .unwrap();
        }

        // ReduceAdd: sum registers 1-5 into register 10
        execute_reduce_add(&mut state, Type::I32, Register(10), Register(1), 5).unwrap();

        let result = state.current_lane().registers.read_i32(Register(10)).unwrap();
        assert_eq!(result, 1 + 2 + 3 + 4 + 5); // 15
    }

    #[test]
    fn test_reduce_min_i32() {
        let mut state = create_test_state();

        let values = [10, 5, 20, 3, 15];
        for (i, &val) in values.iter().enumerate() {
            state
                .current_lane_mut()
                .registers
                .write_i32(Register(i as u8 + 1), val)
                .unwrap();
        }

        execute_reduce_min(&mut state, Type::I32, Register(10), Register(1), 5).unwrap();

        let result = state.current_lane().registers.read_i32(Register(10)).unwrap();
        assert_eq!(result, 3);
    }

    #[test]
    fn test_reduce_max_i32() {
        let mut state = create_test_state();

        let values = [10, 5, 20, 3, 15];
        for (i, &val) in values.iter().enumerate() {
            state
                .current_lane_mut()
                .registers
                .write_i32(Register(i as u8 + 1), val)
                .unwrap();
        }

        execute_reduce_max(&mut state, Type::I32, Register(10), Register(1), 5).unwrap();

        let result = state.current_lane().registers.read_i32(Register(10)).unwrap();
        assert_eq!(result, 20);
    }

    #[test]
    fn test_reduce_mul_i32() {
        let mut state = create_test_state();

        for i in 0..4 {
            state
                .current_lane_mut()
                .registers
                .write_i32(Register(i + 1), (i + 2) as i32)
                .unwrap();
        }

        execute_reduce_mul(&mut state, Type::I32, Register(10), Register(1), 4).unwrap();

        let result = state.current_lane().registers.read_i32(Register(10)).unwrap();
        assert_eq!(result, 2 * 3 * 4 * 5); // 120
    }

    // ================================================================================================
    // Pool Instructions
    // ================================================================================================

    #[test]
    fn test_pool_alloc() {
        let mut state = create_test_state();

        // Allocate a pool of 1024 bytes
        execute_pool_alloc(&mut state, 1024, Register(1)).unwrap();

        // Verify pool handle is stored in register
        let handle = state.current_lane().registers.read_u64(Register(1)).unwrap();
        assert!(handle > 0);
    }

    #[test]
    fn test_pool_load_store() {
        let mut state = create_test_state();

        // Allocate pool
        execute_pool_alloc(&mut state, 1024, Register(1)).unwrap();

        // Store value at offset 0
        state.current_lane_mut().registers.write_f32(Register(2), 42.5).unwrap();
        state.current_lane_mut().registers.write_u64(Register(3), 0).unwrap(); // offset
        execute_pool_store(&mut state, Type::F32, Register(1), Register(3), Register(2)).unwrap();

        // Load value back
        execute_pool_load(&mut state, Type::F32, Register(1), Register(3), Register(4)).unwrap();

        let result = state.current_lane().registers.read_f32(Register(4)).unwrap();
        assert_eq!(result, 42.5);

        // Clean up
        execute_pool_free(&mut state, Register(1)).unwrap();
    }
}
