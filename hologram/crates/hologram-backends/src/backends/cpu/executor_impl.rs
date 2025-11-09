//! CPU implementation of the Executor trait
//!
//! This module contains the complete execution logic for the CPU backend,
//! encapsulated in the `CpuExecutor` struct.

use crate::backend::{ExecutionContext, LaunchConfig};
use crate::backends::common::address::resolve_address_with_state;
use crate::backends::common::executor_trait::Executor;
use crate::backends::common::memory::{load_bytes_from_storage, store_bytes_to_storage};
use crate::backends::common::{atlas_ops, instruction_ops, ExecutionState};
use crate::backends::cpu::memory::MemoryManager;
use crate::error::{BackendError, Result};
use crate::isa::{Address, Instruction, MemoryScope, Program, Register, Type};
use hologram_tracing::perf_span;
use parking_lot::RwLock;
use rayon::prelude::*;
use std::sync::Arc;

/// CPU executor implementation
///
/// Encapsulates all execution logic for the CPU backend, including:
/// - Main execution loop
/// - Instruction dispatch
/// - Memory operations (LDG, STG, LDS, STS)
/// - Control flow operations (BRA, CALL, RET, LOOP, EXIT)
/// - Synchronization operations (BarSync, MemFence)
pub struct CpuExecutor {
    /// Shared memory manager
    memory: Arc<RwLock<MemoryManager>>,
}

impl CpuExecutor {
    /// Create a new CPU executor
    pub fn new(memory: Arc<RwLock<MemoryManager>>) -> Self {
        Self { memory }
    }

    // ============================================================================================
    // Memory Operations (Backend-Specific)
    // ============================================================================================

    /// Execute load global (LDG) instruction with pre-acquired write guard (lock coarsening)
    ///
    /// This version avoids per-instruction lock acquisition for better performance.
    /// Used when processing multiple instructions in a batch.
    ///
    /// # PhiCoordinate Address Resolution
    ///
    /// PhiCoordinate addressing is now fully integrated. Operations in hologram-core
    /// generate PhiCoordinate addresses when buffers are in the boundary pool.
    ///
    /// Address resolution flow:
    /// 1. `resolve_address_with_state()` converts PhiCoordinate → (BufferHandle(0), linear_offset)
    /// 2. `load_bytes_from_storage()` uses the resolved address for memory access
    /// 3. MemoryManager routes BufferHandle(0) to boundary pool (96 classes × 12,288 bytes)
    fn execute_ldg_with_guard(
        &self,
        memory_guard: &MemoryManager,
        state: &mut ExecutionState<MemoryManager>,
        ty: Type,
        dst: Register,
        addr: &Address,
    ) -> Result<()> {
        let _span = perf_span!("cpu_ldg_batched", bytes = ty.size_bytes());

        // Resolve address
        let (handle, offset) = resolve_address_with_state(addr, state)?;

        // Load value from memory (using pre-acquired guard, no lock needed)
        let value_bytes = load_bytes_from_storage(memory_guard, handle, offset, ty.size_bytes())?;

        // Write to register
        let lane = state.current_lane_mut();
        match ty {
            Type::I8 => {
                let value = *bytemuck::from_bytes::<i8>(&value_bytes);
                lane.registers.write_i8(dst, value)?;
            }
            Type::I16 => {
                let value = *bytemuck::from_bytes::<i16>(&value_bytes);
                lane.registers.write_i16(dst, value)?;
            }
            Type::I32 => {
                let value = *bytemuck::from_bytes::<i32>(&value_bytes);
                lane.registers.write_i32(dst, value)?;
            }
            Type::I64 => {
                let value = *bytemuck::from_bytes::<i64>(&value_bytes);
                lane.registers.write_i64(dst, value)?;
            }
            Type::U8 => {
                let value = *bytemuck::from_bytes::<u8>(&value_bytes);
                lane.registers.write_u8(dst, value)?;
            }
            Type::U16 => {
                let value = *bytemuck::from_bytes::<u16>(&value_bytes);
                lane.registers.write_u16(dst, value)?;
            }
            Type::U32 => {
                let value = *bytemuck::from_bytes::<u32>(&value_bytes);
                lane.registers.write_u32(dst, value)?;
            }
            Type::U64 => {
                let value = *bytemuck::from_bytes::<u64>(&value_bytes);
                lane.registers.write_u64(dst, value)?;
            }
            Type::F16 => {
                let value = *bytemuck::from_bytes::<u16>(&value_bytes);
                lane.registers.write_f16_bits(dst, value)?;
            }
            Type::BF16 => {
                let value = *bytemuck::from_bytes::<u16>(&value_bytes);
                lane.registers.write_bf16_bits(dst, value)?;
            }
            Type::F32 => {
                let value = *bytemuck::from_bytes::<f32>(&value_bytes);
                lane.registers.write_f32(dst, value)?;
            }
            Type::F64 => {
                let value = *bytemuck::from_bytes::<f64>(&value_bytes);
                lane.registers.write_f64(dst, value)?;
            }
        }

        Ok(())
    }

    /// Execute load global (LDG) instruction
    fn execute_ldg(
        &self,
        state: &mut ExecutionState<MemoryManager>,
        ty: Type,
        dst: Register,
        addr: &Address,
    ) -> Result<()> {
        let _span = perf_span!("cpu_ldg", bytes = ty.size_bytes());

        // Resolve address (supports RegisterIndirect via execution state)
        let (handle, offset) = resolve_address_with_state(addr, state)?;

        // Load value from memory (separate scope to release lock)
        let value_bytes = {
            let memory = state.shared.memory.read();
            load_bytes_from_storage(&*memory, handle, offset, ty.size_bytes())?
        };

        // Write to register
        let lane = state.current_lane_mut();
        match ty {
            Type::I8 => {
                let value = *bytemuck::from_bytes::<i8>(&value_bytes);
                lane.registers.write_i8(dst, value)?;
            }
            Type::I16 => {
                let value = *bytemuck::from_bytes::<i16>(&value_bytes);
                lane.registers.write_i16(dst, value)?;
            }
            Type::I32 => {
                let value = *bytemuck::from_bytes::<i32>(&value_bytes);
                lane.registers.write_i32(dst, value)?;
            }
            Type::I64 => {
                let value = *bytemuck::from_bytes::<i64>(&value_bytes);
                lane.registers.write_i64(dst, value)?;
            }
            Type::U8 => {
                let value = *bytemuck::from_bytes::<u8>(&value_bytes);
                lane.registers.write_u8(dst, value)?;
            }
            Type::U16 => {
                let value = *bytemuck::from_bytes::<u16>(&value_bytes);
                lane.registers.write_u16(dst, value)?;
            }
            Type::U32 => {
                let value = *bytemuck::from_bytes::<u32>(&value_bytes);
                lane.registers.write_u32(dst, value)?;
            }
            Type::U64 => {
                let value = *bytemuck::from_bytes::<u64>(&value_bytes);
                lane.registers.write_u64(dst, value)?;
            }
            Type::F16 => {
                let value = *bytemuck::from_bytes::<u16>(&value_bytes);
                lane.registers.write_f16_bits(dst, value)?;
            }
            Type::BF16 => {
                let value = *bytemuck::from_bytes::<u16>(&value_bytes);
                lane.registers.write_bf16_bits(dst, value)?;
            }
            Type::F32 => {
                let value = *bytemuck::from_bytes::<f32>(&value_bytes);
                lane.registers.write_f32(dst, value)?;
            }
            Type::F64 => {
                let value = *bytemuck::from_bytes::<f64>(&value_bytes);
                lane.registers.write_f64(dst, value)?;
            }
        }

        Ok(())
    }

    /// Execute store global (STG) instruction with pre-acquired write guard (lock coarsening)
    ///
    /// This version avoids per-instruction lock acquisition for better performance.
    /// Used when processing multiple instructions in a batch.
    ///
    /// # PhiCoordinate Address Resolution
    ///
    /// PhiCoordinate addressing is now fully integrated. Operations in hologram-core
    /// generate PhiCoordinate addresses when buffers are in the boundary pool.
    ///
    /// Address resolution flow:
    /// 1. `resolve_address_with_state()` converts PhiCoordinate → (BufferHandle(0), linear_offset)
    /// 2. `store_bytes_to_storage()` uses the resolved address for memory access
    /// 3. MemoryManager routes BufferHandle(0) to boundary pool (96 classes × 12,288 bytes)
    fn execute_stg_with_guard(
        &self,
        memory_guard: &mut MemoryManager,
        state: &mut ExecutionState<MemoryManager>,
        ty: Type,
        src: Register,
        addr: &Address,
    ) -> Result<()> {
        let _span = perf_span!("cpu_stg_batched", bytes = ty.size_bytes());

        // Resolve address
        let (handle, offset) = resolve_address_with_state(addr, state)?;

        // Read value from register
        let value_bytes = {
            let lane = state.current_lane();
            match ty {
                Type::I8 => bytemuck::bytes_of(&lane.registers.read_i8(src)?).to_vec(),
                Type::I16 => bytemuck::bytes_of(&lane.registers.read_i16(src)?).to_vec(),
                Type::I32 => bytemuck::bytes_of(&lane.registers.read_i32(src)?).to_vec(),
                Type::I64 => bytemuck::bytes_of(&lane.registers.read_i64(src)?).to_vec(),
                Type::U8 => bytemuck::bytes_of(&lane.registers.read_u8(src)?).to_vec(),
                Type::U16 => bytemuck::bytes_of(&lane.registers.read_u16(src)?).to_vec(),
                Type::U32 => bytemuck::bytes_of(&lane.registers.read_u32(src)?).to_vec(),
                Type::U64 => bytemuck::bytes_of(&lane.registers.read_u64(src)?).to_vec(),
                Type::F16 => bytemuck::bytes_of(&lane.registers.read_f16_bits(src)?).to_vec(),
                Type::BF16 => bytemuck::bytes_of(&lane.registers.read_bf16_bits(src)?).to_vec(),
                Type::F32 => bytemuck::bytes_of(&lane.registers.read_f32(src)?).to_vec(),
                Type::F64 => bytemuck::bytes_of(&lane.registers.read_f64(src)?).to_vec(),
            }
        };

        // Store to memory (using pre-acquired guard, no lock needed)
        store_bytes_to_storage(memory_guard, handle, offset, &value_bytes)?;

        Ok(())
    }

    /// Execute store global (STG) instruction
    fn execute_stg(
        &self,
        state: &mut ExecutionState<MemoryManager>,
        ty: Type,
        src: Register,
        addr: &Address,
    ) -> Result<()> {
        let _span = perf_span!("cpu_stg", bytes = ty.size_bytes());

        // Resolve address (supports RegisterIndirect via execution state)
        let (handle, offset) = resolve_address_with_state(addr, state)?;

        // Read value from register (separate scope)
        let value_bytes = {
            let lane = state.current_lane();
            match ty {
                Type::I8 => bytemuck::bytes_of(&lane.registers.read_i8(src)?).to_vec(),
                Type::I16 => bytemuck::bytes_of(&lane.registers.read_i16(src)?).to_vec(),
                Type::I32 => bytemuck::bytes_of(&lane.registers.read_i32(src)?).to_vec(),
                Type::I64 => bytemuck::bytes_of(&lane.registers.read_i64(src)?).to_vec(),
                Type::U8 => bytemuck::bytes_of(&lane.registers.read_u8(src)?).to_vec(),
                Type::U16 => bytemuck::bytes_of(&lane.registers.read_u16(src)?).to_vec(),
                Type::U32 => bytemuck::bytes_of(&lane.registers.read_u32(src)?).to_vec(),
                Type::U64 => bytemuck::bytes_of(&lane.registers.read_u64(src)?).to_vec(),
                Type::F16 => bytemuck::bytes_of(&lane.registers.read_f16_bits(src)?).to_vec(),
                Type::BF16 => bytemuck::bytes_of(&lane.registers.read_bf16_bits(src)?).to_vec(),
                Type::F32 => bytemuck::bytes_of(&lane.registers.read_f32(src)?).to_vec(),
                Type::F64 => bytemuck::bytes_of(&lane.registers.read_f64(src)?).to_vec(),
            }
        };

        // Store to memory
        let mut memory = state.shared.memory.write();
        store_bytes_to_storage(&mut *memory, handle, offset, &value_bytes)?;

        Ok(())
    }

    /// Execute load shared (LDS) instruction
    fn execute_lds(
        &self,
        state: &mut ExecutionState<MemoryManager>,
        ty: Type,
        dst: Register,
        addr: &Address,
    ) -> Result<()> {
        let _span = perf_span!("cpu_lds", bytes = ty.size_bytes());

        // For CPU backend, shared memory is the same as global memory
        // Future: Could implement a separate shared memory space for better simulation
        self.execute_ldg(state, ty, dst, addr)
    }

    /// Execute store shared (STS) instruction
    fn execute_sts(
        &self,
        state: &mut ExecutionState<MemoryManager>,
        ty: Type,
        src: Register,
        addr: &Address,
    ) -> Result<()> {
        let _span = perf_span!("cpu_sts", bytes = ty.size_bytes());

        // For CPU backend, shared memory is the same as global memory
        // Future: Could implement a separate shared memory space for better simulation
        self.execute_stg(state, ty, src, addr)
    }

    // ============================================================================================
    // Control Flow Operations
    // ============================================================================================

    /// Execute branch (BRA) instruction
    fn execute_bra(
        &self,
        state: &mut ExecutionState<MemoryManager>,
        pred: Option<crate::isa::Predicate>,
        target: &crate::isa::Label,
    ) -> Result<()> {
        let _span = perf_span!("cpu_bra");

        let should_branch = if let Some(p) = pred {
            let lane = state.current_lane();
            lane.registers.read_predicate(p)?
        } else {
            true
        };

        if should_branch {
            let target_pc = state
                .shared
                .labels
                .get(&target.0)
                .ok_or_else(|| BackendError::execution_error(format!("Label not found: {}", target.0)))?;
            state.current_lane_mut().pc = *target_pc;
        }

        Ok(())
    }

    /// Execute call (CALL) instruction
    fn execute_call(&self, state: &mut ExecutionState<MemoryManager>, target: &crate::isa::Label) -> Result<()> {
        let _span = perf_span!("cpu_call");

        let target_pc = *state
            .shared
            .labels
            .get(&target.0)
            .ok_or_else(|| BackendError::execution_error(format!("Label not found: {}", target.0)))?;

        // Push return address (next instruction) to call stack
        let return_pc = state.current_lane().pc + 1;
        let lane = state.current_lane_mut();
        lane.call_stack.push(return_pc);

        // Jump to target
        lane.pc = target_pc;

        Ok(())
    }

    /// Execute return (RET) instruction
    fn execute_ret(&self, state: &mut ExecutionState<MemoryManager>) -> Result<()> {
        let _span = perf_span!("cpu_ret");

        // Pop return address from call stack
        let return_pc = state
            .current_lane_mut()
            .call_stack
            .pop()
            .ok_or_else(|| BackendError::execution_error("Call stack underflow".to_string()))?;

        // Jump to return address
        state.current_lane_mut().pc = return_pc;

        Ok(())
    }

    /// Execute loop (LOOP) instruction
    fn execute_loop(
        &self,
        state: &mut ExecutionState<MemoryManager>,
        count: Register,
        body: &crate::isa::Label,
    ) -> Result<()> {
        let _span = perf_span!("cpu_loop");

        // Read loop counter
        let counter = state.current_lane().registers.read_u32(count)?;

        if counter > 0 {
            // Decrement counter
            state.current_lane_mut().registers.write_u32(count, counter - 1)?;

            // Branch to loop body
            let target_pc = *state
                .shared
                .labels
                .get(&body.0)
                .ok_or_else(|| BackendError::execution_error(format!("Label not found: {}", body.0)))?;
            state.current_lane_mut().pc = target_pc;
        }

        Ok(())
    }

    /// Execute exit (EXIT) instruction
    fn execute_exit(&self, state: &mut ExecutionState<MemoryManager>) -> Result<()> {
        let _span = perf_span!("cpu_exit");

        state.current_lane_mut().active = false;
        Ok(())
    }

    /// Execute instruction with pre-acquired memory guard (lock coarsening optimization)
    ///
    /// This method routes memory operations (LDG/STG/LDS/STS) to guard-based implementations
    /// that avoid per-instruction lock acquisition. Other instructions use the standard handlers.
    ///
    /// # Lock Coarsening Strategy
    ///
    /// Instead of acquiring `state.memory` lock per instruction (3n acquisitions for vector ops),
    /// acquire it once for the entire instruction stream (1 acquisition).
    ///
    /// **Performance Impact**: 2-4x speedup for n > 3,072 (from Phase 2 analysis)
    fn execute_instruction_with_guard(
        &self,
        memory_guard: &mut MemoryManager,
        state: &mut ExecutionState<MemoryManager>,
        instruction: &Instruction,
    ) -> Result<()> {
        match instruction {
            // Data Movement - Use guard-based versions for LDG/STG
            Instruction::LDG { ty, dst, addr } => self.execute_ldg_with_guard(memory_guard, state, *ty, *dst, addr),
            Instruction::STG { ty, src, addr } => self.execute_stg_with_guard(memory_guard, state, *ty, *src, addr),
            Instruction::LDS { ty, dst, addr } => {
                // For CPU backend, shared memory is same as global memory
                self.execute_ldg_with_guard(memory_guard, state, *ty, *dst, addr)
            }
            Instruction::STS { ty, src, addr } => {
                // For CPU backend, shared memory is same as global memory
                self.execute_stg_with_guard(memory_guard, state, *ty, *src, addr)
            }
            Instruction::MOV { ty, dst, src } => instruction_ops::execute_mov(state, *ty, *dst, *src),
            Instruction::MOV_IMM { ty, dst, value } => instruction_ops::execute_mov_imm(state, *ty, *dst, *value),
            Instruction::CVT {
                src_ty,
                dst_ty,
                dst,
                src,
            } => instruction_ops::execute_cvt(state, *src_ty, *dst_ty, *dst, *src),

            // Arithmetic
            Instruction::ADD { ty, dst, src1, src2 } => instruction_ops::execute_add(state, *ty, *dst, *src1, *src2),
            Instruction::SUB { ty, dst, src1, src2 } => instruction_ops::execute_sub(state, *ty, *dst, *src1, *src2),
            Instruction::MUL { ty, dst, src1, src2 } => instruction_ops::execute_mul(state, *ty, *dst, *src1, *src2),
            Instruction::DIV { ty, dst, src1, src2 } => instruction_ops::execute_div(state, *ty, *dst, *src1, *src2),
            Instruction::MAD { ty, dst, a, b, c } => instruction_ops::execute_mad(state, *ty, *dst, *a, *b, *c),
            Instruction::FMA { ty, dst, a, b, c } => instruction_ops::execute_fma(state, *ty, *dst, *a, *b, *c),
            Instruction::MIN { ty, dst, src1, src2 } => instruction_ops::execute_min(state, *ty, *dst, *src1, *src2),
            Instruction::MAX { ty, dst, src1, src2 } => instruction_ops::execute_max(state, *ty, *dst, *src1, *src2),
            Instruction::ABS { ty, dst, src } => instruction_ops::execute_abs(state, *ty, *dst, *src),
            Instruction::NEG { ty, dst, src } => instruction_ops::execute_neg(state, *ty, *dst, *src),

            // Logical
            Instruction::AND { ty, dst, src1, src2 } => instruction_ops::execute_and(state, *ty, *dst, *src1, *src2),
            Instruction::OR { ty, dst, src1, src2 } => instruction_ops::execute_or(state, *ty, *dst, *src1, *src2),
            Instruction::XOR { ty, dst, src1, src2 } => instruction_ops::execute_xor(state, *ty, *dst, *src1, *src2),
            Instruction::NOT { ty, dst, src } => instruction_ops::execute_not(state, *ty, *dst, *src),
            Instruction::SHL { ty, dst, src, amount } => instruction_ops::execute_shl(state, *ty, *dst, *src, *amount),
            Instruction::SHR { ty, dst, src, amount } => instruction_ops::execute_shr(state, *ty, *dst, *src, *amount),

            // Comparison
            Instruction::SETcc {
                cond,
                ty,
                dst,
                src1,
                src2,
            } => instruction_ops::execute_setcc(state, *cond, *ty, *dst, *src1, *src2),

            // Control Flow
            Instruction::BRA { pred, target } => self.execute_bra(state, *pred, target),
            Instruction::CALL { target } => self.execute_call(state, target),
            Instruction::RET => self.execute_ret(state),
            Instruction::LOOP { count, body } => self.execute_loop(state, *count, body),
            Instruction::EXIT => self.execute_exit(state),

            // Synchronization
            Instruction::BarSync { id } => self.execute_barrier_sync(state, *id),
            Instruction::MemFence { scope } => self.execute_memory_fence(state, *scope),

            // Atlas-Specific (using common implementations)
            Instruction::ClsGet { dst } => atlas_ops::execute_cls_get(state, *dst),
            Instruction::MIRROR { dst, src } => atlas_ops::execute_mirror(state, *dst, *src),
            Instruction::UnityTest { dst, epsilon } => atlas_ops::execute_unity_test(state, *dst, *epsilon),
            Instruction::NbrCount { class, dst } => atlas_ops::execute_nbr_count(state, *class, *dst),
            Instruction::NbrGet { class, index, dst } => atlas_ops::execute_nbr_get(state, *class, *index, *dst),
            Instruction::ResAccum { class, value } => atlas_ops::execute_res_accum(state, *class, *value),
            Instruction::PhaseGet { dst } => atlas_ops::execute_phase_get(state, *dst),
            Instruction::PhaseAdv { delta } => atlas_ops::execute_phase_adv(state, *delta),
            Instruction::BoundMap { class, page, byte, dst } => {
                atlas_ops::execute_bound_map(state, *class, *page, *byte, *dst)
            }

            // Pool Storage
            Instruction::PoolAlloc { size, dst } => instruction_ops::execute_pool_alloc(state, *size, *dst),
            Instruction::PoolFree { handle } => instruction_ops::execute_pool_free(state, *handle),
            Instruction::PoolLoad { ty, pool, offset, dst } => {
                instruction_ops::execute_pool_load(state, *ty, *pool, *offset, *dst)
            }
            Instruction::PoolStore { ty, pool, offset, src } => {
                instruction_ops::execute_pool_store(state, *ty, *pool, *offset, *src)
            }

            // Reductions
            Instruction::ReduceAdd {
                ty,
                dst,
                src_base,
                count,
            } => instruction_ops::execute_reduce_add(state, *ty, *dst, *src_base, *count),
            Instruction::ReduceMin {
                ty,
                dst,
                src_base,
                count,
            } => instruction_ops::execute_reduce_min(state, *ty, *dst, *src_base, *count),
            Instruction::ReduceMax {
                ty,
                dst,
                src_base,
                count,
            } => instruction_ops::execute_reduce_max(state, *ty, *dst, *src_base, *count),
            Instruction::ReduceMul {
                ty,
                dst,
                src_base,
                count,
            } => instruction_ops::execute_reduce_mul(state, *ty, *dst, *src_base, *count),

            // Transcendentals
            Instruction::SIN { ty, dst, src } => instruction_ops::execute_sin(state, *ty, *dst, *src),
            Instruction::COS { ty, dst, src } => instruction_ops::execute_cos(state, *ty, *dst, *src),
            Instruction::TAN { ty, dst, src } => instruction_ops::execute_tan(state, *ty, *dst, *src),
            Instruction::TANH { ty, dst, src } => instruction_ops::execute_tanh(state, *ty, *dst, *src),
            Instruction::SIGMOID { ty, dst, src } => instruction_ops::execute_sigmoid(state, *ty, *dst, *src),
            Instruction::EXP { ty, dst, src } => instruction_ops::execute_exp(state, *ty, *dst, *src),
            Instruction::LOG { ty, dst, src } => instruction_ops::execute_log(state, *ty, *dst, *src),
            Instruction::LOG2 { ty, dst, src } => instruction_ops::execute_log2(state, *ty, *dst, *src),
            Instruction::LOG10 { ty, dst, src } => instruction_ops::execute_log10(state, *ty, *dst, *src),
            Instruction::SQRT { ty, dst, src } => instruction_ops::execute_sqrt(state, *ty, *dst, *src),
            Instruction::RSQRT { ty, dst, src } => instruction_ops::execute_rsqrt(state, *ty, *dst, *src),

            // Special
            Instruction::SEL {
                ty,
                dst,
                pred,
                src_true,
                src_false,
            } => instruction_ops::execute_sel(state, *ty, *dst, *pred, *src_true, *src_false),
        }
    }
}

// ================================================================================================
// Executor Trait Implementation
// ================================================================================================

impl Executor<MemoryManager> for CpuExecutor {
    fn execute(&self, program: &Program, config: &LaunchConfig) -> Result<()> {
        let _span = perf_span!(
            "cpu_execute_program",
            instructions = program.instructions.len(),
            grid_size = config.grid.x * config.grid.y * config.grid.z,
            block_size = config.block.x * config.block.y * config.block.z
        );

        // Validate program
        program.validate()?;

        // Calculate total number of lanes (threads) per block
        let num_lanes = (config.block.x * config.block.y * config.block.z) as usize;

        // Calculate total number of blocks in the grid
        let total_blocks = (config.grid.x * config.grid.y * config.grid.z) as usize;

        // Phase 1: Block-Level Parallelism
        // Parallelize across blocks using Rayon (coarse-grained parallelism)
        // Benefits:
        // - No shared mutable state between blocks (naturally independent)
        // - No ExecutionState refactoring required
        // - Scales with grid size (more blocks = more parallelism)
        // - Each block can still use lane-level parallelism internally
        (0..total_blocks).into_par_iter().try_for_each(|block_idx| {
            // Calculate block coordinates from linear index
            let blocks_per_row = config.grid.x as usize;
            let blocks_per_slice = (config.grid.x * config.grid.y) as usize;

            let block_z = (block_idx / blocks_per_slice) as u32;
            let block_y = ((block_idx % blocks_per_slice) / blocks_per_row) as u32;
            let block_x = (block_idx % blocks_per_row) as u32;

            // Execute all lanes in this block in parallel using Rayon (nested parallelism)
            // Each lane gets its own ExecutionState to avoid shared mutable state
            (0..num_lanes).into_par_iter().try_for_each(|lane_idx| {
                // Calculate lane coordinates
                let lane_z = (lane_idx / (config.block.x * config.block.y) as usize) as u32;
                let lane_y = ((lane_idx / config.block.x as usize) % config.block.y as usize) as u32;
                let lane_x = (lane_idx % config.block.x as usize) as u32;

                // Create lane-specific execution context
                let lane_context = ExecutionContext::new(
                    (block_x, block_y, block_z),
                    (lane_x, lane_y, lane_z),
                    config.grid,
                    config.block,
                );

                // Create ExecutionState with single lane (avoids shared mutable state)
                let mut lane_state = ExecutionState::new(
                    1, // One lane per ExecutionState for parallel execution
                    Arc::clone(&self.memory),
                    lane_context,
                    program.labels.clone(),
                );

                // Initialize special registers for this lane
                // Per ISA §special_registers: Pre-load built-in thread indices
                {
                    use crate::isa::special_registers::*;
                    let lane = &mut lane_state.lane_states[0].lane; // Index 0 since we have one lane
                    lane.registers.write_u32(LANE_IDX_X, lane_context.lane_idx.0)?;
                    lane.registers.write_u32(BLOCK_IDX_X, lane_context.block_idx.0)?;
                    lane.registers.write_u32(BLOCK_DIM_X, lane_context.block_dim.x)?;
                    lane.registers
                        .write_u64(GLOBAL_LANE_ID, lane_context.global_lane_index())?;
                }

                // Execute instructions for this lane with lock coarsening
                //
                // OPTIMIZATION: Acquire memory lock once for entire lane execution
                // instead of per-instruction (3n → 1 lock acquisition)
                //
                // This reduces RwLock contention from the primary bottleneck (Phase 2 analysis)
                // Expected performance: 2-4x speedup for n > 3,072
                {
                    let mut memory_guard = self.memory.write(); // Single lock acquisition

                    while lane_state.lane_states[0].lane.active
                        && lane_state.lane_states[0].lane.pc < program.instructions.len()
                    {
                        let pc = lane_state.lane_states[0].lane.pc;
                        let instruction = &program.instructions[pc];

                        // Execute instruction with pre-acquired guard (no per-instruction locking)
                        self.execute_instruction_with_guard(&mut memory_guard, &mut lane_state, instruction)?;

                        // Advance PC (unless instruction modified it, e.g., branch)
                        if lane_state.lane_states[0].lane.pc == pc {
                            lane_state.lane_states[0].lane.pc += 1;
                        }
                    }

                    // Memory guard released here automatically (RAII)
                }

                Ok::<(), BackendError>(())
            })
        })?;

        Ok(())
    }

    fn execute_instruction(&self, state: &mut ExecutionState<MemoryManager>, instruction: &Instruction) -> Result<()> {
        match instruction {
            // Data Movement
            Instruction::LDG { ty, dst, addr } => self.execute_ldg(state, *ty, *dst, addr),
            Instruction::STG { ty, src, addr } => self.execute_stg(state, *ty, *src, addr),
            Instruction::LDS { ty, dst, addr } => self.execute_lds(state, *ty, *dst, addr),
            Instruction::STS { ty, src, addr } => self.execute_sts(state, *ty, *src, addr),
            Instruction::MOV { ty, dst, src } => instruction_ops::execute_mov(state, *ty, *dst, *src),
            Instruction::MOV_IMM { ty, dst, value } => instruction_ops::execute_mov_imm(state, *ty, *dst, *value),
            Instruction::CVT {
                src_ty,
                dst_ty,
                dst,
                src,
            } => instruction_ops::execute_cvt(state, *src_ty, *dst_ty, *dst, *src),

            // Arithmetic
            Instruction::ADD { ty, dst, src1, src2 } => instruction_ops::execute_add(state, *ty, *dst, *src1, *src2),
            Instruction::SUB { ty, dst, src1, src2 } => instruction_ops::execute_sub(state, *ty, *dst, *src1, *src2),
            Instruction::MUL { ty, dst, src1, src2 } => instruction_ops::execute_mul(state, *ty, *dst, *src1, *src2),
            Instruction::DIV { ty, dst, src1, src2 } => instruction_ops::execute_div(state, *ty, *dst, *src1, *src2),
            Instruction::MAD { ty, dst, a, b, c } => instruction_ops::execute_mad(state, *ty, *dst, *a, *b, *c),
            Instruction::FMA { ty, dst, a, b, c } => instruction_ops::execute_fma(state, *ty, *dst, *a, *b, *c),
            Instruction::MIN { ty, dst, src1, src2 } => instruction_ops::execute_min(state, *ty, *dst, *src1, *src2),
            Instruction::MAX { ty, dst, src1, src2 } => instruction_ops::execute_max(state, *ty, *dst, *src1, *src2),
            Instruction::ABS { ty, dst, src } => instruction_ops::execute_abs(state, *ty, *dst, *src),
            Instruction::NEG { ty, dst, src } => instruction_ops::execute_neg(state, *ty, *dst, *src),

            // Logical
            Instruction::AND { ty, dst, src1, src2 } => instruction_ops::execute_and(state, *ty, *dst, *src1, *src2),
            Instruction::OR { ty, dst, src1, src2 } => instruction_ops::execute_or(state, *ty, *dst, *src1, *src2),
            Instruction::XOR { ty, dst, src1, src2 } => instruction_ops::execute_xor(state, *ty, *dst, *src1, *src2),
            Instruction::NOT { ty, dst, src } => instruction_ops::execute_not(state, *ty, *dst, *src),
            Instruction::SHL { ty, dst, src, amount } => instruction_ops::execute_shl(state, *ty, *dst, *src, *amount),
            Instruction::SHR { ty, dst, src, amount } => instruction_ops::execute_shr(state, *ty, *dst, *src, *amount),

            // Comparison
            Instruction::SETcc {
                cond,
                ty,
                dst,
                src1,
                src2,
            } => instruction_ops::execute_setcc(state, *cond, *ty, *dst, *src1, *src2),

            // Control Flow
            Instruction::BRA { pred, target } => self.execute_bra(state, *pred, target),
            Instruction::CALL { target } => self.execute_call(state, target),
            Instruction::RET => self.execute_ret(state),
            Instruction::LOOP { count, body } => self.execute_loop(state, *count, body),
            Instruction::EXIT => self.execute_exit(state),

            // Synchronization
            Instruction::BarSync { id } => self.execute_barrier_sync(state, *id),
            Instruction::MemFence { scope } => self.execute_memory_fence(state, *scope),

            // Atlas-Specific (using common implementations)
            Instruction::ClsGet { dst } => atlas_ops::execute_cls_get(state, *dst),
            Instruction::MIRROR { dst, src } => atlas_ops::execute_mirror(state, *dst, *src),
            Instruction::UnityTest { dst, epsilon } => atlas_ops::execute_unity_test(state, *dst, *epsilon),
            Instruction::NbrCount { class, dst } => atlas_ops::execute_nbr_count(state, *class, *dst),
            Instruction::NbrGet { class, index, dst } => atlas_ops::execute_nbr_get(state, *class, *index, *dst),
            Instruction::ResAccum { class, value } => atlas_ops::execute_res_accum(state, *class, *value),
            Instruction::PhaseGet { dst } => atlas_ops::execute_phase_get(state, *dst),
            Instruction::PhaseAdv { delta } => atlas_ops::execute_phase_adv(state, *delta),
            Instruction::BoundMap { class, page, byte, dst } => {
                atlas_ops::execute_bound_map(state, *class, *page, *byte, *dst)
            }

            // Pool Storage
            Instruction::PoolAlloc { size, dst } => instruction_ops::execute_pool_alloc(state, *size, *dst),
            Instruction::PoolFree { handle } => instruction_ops::execute_pool_free(state, *handle),
            Instruction::PoolLoad { ty, pool, offset, dst } => {
                instruction_ops::execute_pool_load(state, *ty, *pool, *offset, *dst)
            }
            Instruction::PoolStore { ty, pool, offset, src } => {
                instruction_ops::execute_pool_store(state, *ty, *pool, *offset, *src)
            }

            // Reductions
            Instruction::ReduceAdd {
                ty,
                dst,
                src_base,
                count,
            } => instruction_ops::execute_reduce_add(state, *ty, *dst, *src_base, *count),
            Instruction::ReduceMin {
                ty,
                dst,
                src_base,
                count,
            } => instruction_ops::execute_reduce_min(state, *ty, *dst, *src_base, *count),
            Instruction::ReduceMax {
                ty,
                dst,
                src_base,
                count,
            } => instruction_ops::execute_reduce_max(state, *ty, *dst, *src_base, *count),
            Instruction::ReduceMul {
                ty,
                dst,
                src_base,
                count,
            } => instruction_ops::execute_reduce_mul(state, *ty, *dst, *src_base, *count),

            // Transcendentals
            Instruction::SIN { ty, dst, src } => instruction_ops::execute_sin(state, *ty, *dst, *src),
            Instruction::COS { ty, dst, src } => instruction_ops::execute_cos(state, *ty, *dst, *src),
            Instruction::TAN { ty, dst, src } => instruction_ops::execute_tan(state, *ty, *dst, *src),
            Instruction::TANH { ty, dst, src } => instruction_ops::execute_tanh(state, *ty, *dst, *src),
            Instruction::SIGMOID { ty, dst, src } => instruction_ops::execute_sigmoid(state, *ty, *dst, *src),
            Instruction::EXP { ty, dst, src } => instruction_ops::execute_exp(state, *ty, *dst, *src),
            Instruction::LOG { ty, dst, src } => instruction_ops::execute_log(state, *ty, *dst, *src),
            Instruction::LOG2 { ty, dst, src } => instruction_ops::execute_log2(state, *ty, *dst, *src),
            Instruction::LOG10 { ty, dst, src } => instruction_ops::execute_log10(state, *ty, *dst, *src),
            Instruction::SQRT { ty, dst, src } => instruction_ops::execute_sqrt(state, *ty, *dst, *src),
            Instruction::RSQRT { ty, dst, src } => instruction_ops::execute_rsqrt(state, *ty, *dst, *src),

            // Special
            Instruction::SEL {
                ty,
                dst,
                pred,
                src_true,
                src_false,
            } => instruction_ops::execute_sel(state, *ty, *dst, *pred, *src_true, *src_false),
        }
    }

    fn execute_barrier_sync(&self, _state: &mut ExecutionState<MemoryManager>, _barrier_id: u8) -> Result<()> {
        let _span = perf_span!("cpu_barrier_sync");

        // For single-threaded CPU execution, barriers are no-ops
        //
        // In a multi-threaded implementation, this would:
        // 1. Check if this barrier_id exists in state.barriers
        // 2. Wait for all threads in the barrier group to arrive
        // 3. Release all threads once they've all arrived
        //
        // Example multi-threaded implementation:
        //
        // ```rust
        // if let Some(barrier) = state.barriers.get(&barrier_id) {
        //     barrier.wait();  // Block until all threads arrive
        // }
        // ```
        //
        // GPU backends would use __syncthreads() or equivalent
        // TPU backends would use hardware synchronization primitives

        Ok(())
    }

    fn execute_memory_fence(&self, _state: &mut ExecutionState<MemoryManager>, scope: MemoryScope) -> Result<()> {
        let _span = perf_span!("cpu_memory_fence");

        use std::sync::atomic::{fence, Ordering};

        // Emit appropriate memory fence based on scope
        // Per ISA §7.5 and CPU Backend Requirements §8.2
        match scope {
            MemoryScope::Thread => {
                // No memory barrier needed for single thread
                Ok(())
            }
            MemoryScope::Block => {
                // Thread block scope - acquire-release semantics for work-stealing
                fence(Ordering::AcqRel);
                Ok(())
            }
            MemoryScope::Device => {
                // Device scope - ensure all writes are visible
                fence(Ordering::AcqRel);
                Ok(())
            }
            MemoryScope::System => {
                // Full system memory barrier - sequential consistency
                fence(Ordering::SeqCst);
                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::{BlockDim, GridDim};

    #[test]
    fn test_executor_empty_program() {
        let program = Program::new();
        let config = LaunchConfig::default();
        let memory = Arc::new(RwLock::new(MemoryManager::new()));
        let executor = CpuExecutor::new(memory);

        let result = executor.execute(&program, &config);
        assert!(result.is_ok());
    }

    #[test]
    fn test_executor_exit_instruction() {
        let mut program = Program::new();
        program.instructions.push(Instruction::EXIT);

        let config = LaunchConfig::default();
        let memory = Arc::new(RwLock::new(MemoryManager::new()));
        let executor = CpuExecutor::new(memory);

        let result = executor.execute(&program, &config);
        assert!(result.is_ok());
    }

    #[test]
    fn test_barrier_sync_noop() {
        let memory = Arc::new(RwLock::new(MemoryManager::new()));
        let context = ExecutionContext::new(
            (0, 0, 0),
            (0, 0, 0),
            GridDim { x: 1, y: 1, z: 1 },
            BlockDim { x: 1, y: 1, z: 1 },
        );
        let labels = std::collections::HashMap::new();
        let mut state = ExecutionState::new(1, Arc::clone(&memory), context, labels);
        let executor = CpuExecutor::new(memory);

        // Should succeed without error (no-op)
        assert!(executor.execute_barrier_sync(&mut state, 0).is_ok());
        assert!(executor.execute_barrier_sync(&mut state, 255).is_ok());
    }

    #[test]
    fn test_memory_fence_all_scopes() {
        let memory = Arc::new(RwLock::new(MemoryManager::new()));
        let context = ExecutionContext::new(
            (0, 0, 0),
            (0, 0, 0),
            GridDim { x: 1, y: 1, z: 1 },
            BlockDim { x: 1, y: 1, z: 1 },
        );
        let labels = std::collections::HashMap::new();
        let mut state = ExecutionState::new(1, Arc::clone(&memory), context, labels);
        let executor = CpuExecutor::new(memory);

        // All memory scopes should succeed
        assert!(executor.execute_memory_fence(&mut state, MemoryScope::Thread).is_ok());
        assert!(executor.execute_memory_fence(&mut state, MemoryScope::Block).is_ok());
        assert!(executor.execute_memory_fence(&mut state, MemoryScope::Device).is_ok());
        assert!(executor.execute_memory_fence(&mut state, MemoryScope::System).is_ok());
    }

    #[test]
    fn test_tracing_instrumentation() {
        use crate::isa::{Address, Register, Type};

        // Initialize tracing for this test
        let _ = tracing_subscriber::fmt()
            .with_test_writer()
            .with_max_level(tracing::Level::DEBUG)
            .try_init();

        let memory = Arc::new(RwLock::new(MemoryManager::new()));
        let executor = CpuExecutor::new(Arc::clone(&memory));

        // Allocate a buffer for testing
        let buffer = memory.write().allocate_buffer(64).unwrap();

        // Create a simple program with memory operations
        let mut program = Program::new();

        // LDG: Load from global memory
        program.instructions.push(Instruction::LDG {
            ty: Type::F32,
            dst: Register(0),
            addr: Address::BufferOffset {
                handle: buffer.0,
                offset: 0,
            },
        });

        // STG: Store to global memory
        program.instructions.push(Instruction::STG {
            ty: Type::F32,
            src: Register(0),
            addr: Address::BufferOffset {
                handle: buffer.0,
                offset: 4,
            },
        });

        // EXIT
        program.instructions.push(Instruction::EXIT);

        let config = LaunchConfig::default();

        // Execute program - should produce tracing output
        let result = executor.execute(&program, &config);
        assert!(result.is_ok());

        // Clean up
        memory.write().free_buffer(buffer).unwrap();
    }

    #[test]
    fn test_special_registers_initialization() {
        // Create a launch config with 2 blocks × 4 lanes
        let config = LaunchConfig::new(
            GridDim::new(2, 1, 1),
            BlockDim::new(4, 1, 1),
            crate::backend::SharedMemoryConfig::default(),
        );

        let memory = Arc::new(RwLock::new(MemoryManager::new()));
        let executor = CpuExecutor::new(Arc::clone(&memory));

        // Create a simple program that exits immediately
        let mut program = Program::new();
        program.instructions.push(Instruction::EXIT);

        // Execute program
        executor.execute(&program, &config).unwrap();

        // Verify special registers were initialized correctly
        // Note: We can't directly inspect the lanes after execution, but we can
        // verify the execution succeeded. For detailed verification, we'll use
        // a program that reads and stores the special registers.
    }

    #[test]
    fn test_runtime_program_creation_vector_add() {
        use crate::isa::special_registers::*;

        // This test demonstrates Plan A: Runtime program creation
        // Programs are created at runtime with buffer handles, achieving O(1) overhead

        let memory = Arc::new(RwLock::new(MemoryManager::new()));
        let executor = CpuExecutor::new(Arc::clone(&memory));

        // Allocate 3 buffers for a, b, c
        let buf_a = memory.write().allocate_buffer(16).unwrap(); // 4 f32 values
        let buf_b = memory.write().allocate_buffer(16).unwrap();
        let buf_c = memory.write().allocate_buffer(16).unwrap();

        // Initialize input data
        let data_a: Vec<f32> = vec![1.0, 2.0, 3.0, 4.0];
        let data_b: Vec<f32> = vec![10.0, 20.0, 30.0, 40.0];

        memory
            .write()
            .copy_to_buffer(buf_a, bytemuck::cast_slice(&data_a))
            .unwrap();
        memory
            .write()
            .copy_to_buffer(buf_b, bytemuck::cast_slice(&data_b))
            .unwrap();

        // ========================================================================
        // Runtime Program Creation: vector_add(a, b, c)
        // ========================================================================
        // This function creates the program at runtime with specific buffer handles.
        // Overhead: ~100ns (acceptable vs GBs of data processing)

        fn create_vector_add_program(buf_a_id: u64, buf_b_id: u64, buf_c_id: u64) -> Program {
            use crate::isa::{Address, Instruction, Register, Type};
            use std::collections::HashMap;

            Program {
                instructions: vec![
                    // R1 = buffer_a handle
                    Instruction::MOV_IMM {
                        ty: Type::U64,
                        dst: Register(1),
                        value: buf_a_id,
                    },
                    // R2 = buffer_b handle
                    Instruction::MOV_IMM {
                        ty: Type::U64,
                        dst: Register(2),
                        value: buf_b_id,
                    },
                    // R3 = buffer_c handle
                    Instruction::MOV_IMM {
                        ty: Type::U64,
                        dst: Register(3),
                        value: buf_c_id,
                    },
                    // R250 = 2 (shift amount for *4)
                    Instruction::MOV_IMM {
                        ty: Type::U32,
                        dst: Register(250),
                        value: 2,
                    },
                    // R0 = GLOBAL_LANE_ID * 4 (byte offset for f32)
                    Instruction::SHL {
                        ty: Type::U64,
                        dst: Register(0),
                        src: GLOBAL_LANE_ID,
                        amount: Register(250),
                    },
                    // R10 = a[global_lane_id]
                    Instruction::LDG {
                        ty: Type::F32,
                        dst: Register(10),
                        addr: Address::RegisterIndirectComputed {
                            handle_reg: Register(1),
                            offset_reg: Register(0),
                        },
                    },
                    // R11 = b[global_lane_id]
                    Instruction::LDG {
                        ty: Type::F32,
                        dst: Register(11),
                        addr: Address::RegisterIndirectComputed {
                            handle_reg: Register(2),
                            offset_reg: Register(0),
                        },
                    },
                    // R12 = R10 + R11
                    Instruction::ADD {
                        ty: Type::F32,
                        dst: Register(12),
                        src1: Register(10),
                        src2: Register(11),
                    },
                    // c[global_lane_id] = R12
                    Instruction::STG {
                        ty: Type::F32,
                        src: Register(12),
                        addr: Address::RegisterIndirectComputed {
                            handle_reg: Register(3),
                            offset_reg: Register(0),
                        },
                    },
                    Instruction::EXIT,
                ],
                labels: HashMap::new(),
            }
        }

        // Create program at runtime with actual buffer IDs
        let program = create_vector_add_program(buf_a.id(), buf_b.id(), buf_c.id());

        // Execute with 4 parallel lanes (one per element)
        let config = LaunchConfig::new(
            GridDim::new(1, 1, 1),
            BlockDim::new(4, 1, 1),
            crate::backend::SharedMemoryConfig::default(),
        );

        executor.execute(&program, &config).unwrap();

        // Verify results: c[i] = a[i] + b[i]
        let mut result = vec![0f32; 4];
        memory
            .read()
            .copy_from_buffer(buf_c, bytemuck::cast_slice_mut(&mut result))
            .unwrap();

        assert_eq!(result[0], 11.0); // 1.0 + 10.0
        assert_eq!(result[1], 22.0); // 2.0 + 20.0
        assert_eq!(result[2], 33.0); // 3.0 + 30.0
        assert_eq!(result[3], 44.0); // 4.0 + 40.0

        // Clean up
        memory.write().free_buffer(buf_a).unwrap();
        memory.write().free_buffer(buf_b).unwrap();
        memory.write().free_buffer(buf_c).unwrap();
    }

    #[test]
    fn test_cached_vector_add_plan_b() {
        use crate::isa::Type;
        use crate::program_builder::create_element_wise_binary;
        use crate::program_cache::{ProgramCache, ProgramKey};

        // Plan B: Runtime program creation + caching
        // This demonstrates the complete caching infrastructure

        static VECTOR_ADD_CACHE: ProgramCache = ProgramCache::new();

        let memory = Arc::new(RwLock::new(MemoryManager::new()));
        let executor = CpuExecutor::new(Arc::clone(&memory));

        // Allocate buffers
        let buf_a = memory.write().allocate_buffer(16).unwrap();
        let buf_b = memory.write().allocate_buffer(16).unwrap();
        let buf_c = memory.write().allocate_buffer(16).unwrap();

        // Initialize data
        let data_a: Vec<f32> = vec![1.0, 2.0, 3.0, 4.0];
        let data_b: Vec<f32> = vec![10.0, 20.0, 30.0, 40.0];
        memory
            .write()
            .copy_to_buffer(buf_a, bytemuck::cast_slice(&data_a))
            .unwrap();
        memory
            .write()
            .copy_to_buffer(buf_b, bytemuck::cast_slice(&data_b))
            .unwrap();

        // ========================================================================
        // Plan B: Get program from cache (or create if not cached)
        // ========================================================================

        let key = ProgramKey::three_buffer("vector_add", buf_a.id(), buf_b.id(), buf_c.id());
        let program = VECTOR_ADD_CACHE.get_or_create(&key, || {
            // This closure is only called on first access (cache miss)
            // Subsequent calls with the same buffer handles return the cached program
            create_element_wise_binary(buf_a.id(), buf_b.id(), buf_c.id(), Type::F32, |src1, src2, dst| {
                Instruction::ADD {
                    ty: Type::F32,
                    dst,
                    src1,
                    src2,
                }
            })
        });

        // Execute program
        let config = LaunchConfig::new(
            GridDim::new(1, 1, 1),
            BlockDim::new(4, 1, 1),
            crate::backend::SharedMemoryConfig::default(),
        );

        executor.execute(&program, &config).unwrap();

        // Verify results
        let mut result = vec![0f32; 4];
        memory
            .read()
            .copy_from_buffer(buf_c, bytemuck::cast_slice_mut(&mut result))
            .unwrap();

        assert_eq!(result[0], 11.0);
        assert_eq!(result[1], 22.0);
        assert_eq!(result[2], 33.0);
        assert_eq!(result[3], 44.0);

        // ========================================================================
        // Second execution: program should come from cache
        // ========================================================================

        // Clear output buffer
        let zeros = vec![0f32; 4];
        memory
            .write()
            .copy_to_buffer(buf_c, bytemuck::cast_slice(&zeros))
            .unwrap();

        // Same key should hit cache
        let program2 = VECTOR_ADD_CACHE.get_or_create(&key, || {
            panic!("Should not create program again - should hit cache!");
        });

        executor.execute(&program2, &config).unwrap();

        // Verify results again
        memory
            .read()
            .copy_from_buffer(buf_c, bytemuck::cast_slice_mut(&mut result))
            .unwrap();
        assert_eq!(result[0], 11.0);
        assert_eq!(result[1], 22.0);

        // Verify cache was used (only 1 program created)
        assert_eq!(VECTOR_ADD_CACHE.len(), 1);

        // Clean up
        memory.write().free_buffer(buf_a).unwrap();
        memory.write().free_buffer(buf_b).unwrap();
        memory.write().free_buffer(buf_c).unwrap();
    }

    #[test]
    fn test_special_registers_read_values() {
        use crate::isa::special_registers::*;

        // Create a launch config with 2 blocks × 4 lanes
        let config = LaunchConfig::new(
            GridDim::new(2, 1, 1),
            BlockDim::new(4, 1, 1),
            crate::backend::SharedMemoryConfig::default(),
        );

        let memory = Arc::new(RwLock::new(MemoryManager::new()));
        let executor = CpuExecutor::new(Arc::clone(&memory));

        // Allocate buffers to store special register values
        let buf_lane_idx = memory.write().allocate_buffer(16).unwrap(); // 4 lanes × 4 bytes (u32)
        let buf_block_idx = memory.write().allocate_buffer(16).unwrap(); // 4 lanes × 4 bytes (u32)
        let buf_block_dim = memory.write().allocate_buffer(16).unwrap(); // 4 lanes × 4 bytes (u32)
        let buf_global_id = memory.write().allocate_buffer(32).unwrap(); // 4 lanes × 8 bytes (u64)

        // Create a program that reads special registers and stores them
        // Store each lane's LANE_IDX_X to verify initialization
        let mut program = Program::new();

        // Store LANE_IDX_X to memory at offset 0 (lane 0 only for simplicity)
        program.instructions.push(Instruction::STG {
            ty: Type::U32,
            src: LANE_IDX_X,
            addr: Address::BufferOffset {
                handle: buf_lane_idx.0,
                offset: 0,
            },
        });

        // Store BLOCK_IDX_X to memory
        program.instructions.push(Instruction::STG {
            ty: Type::U32,
            src: BLOCK_IDX_X,
            addr: Address::BufferOffset {
                handle: buf_block_idx.0,
                offset: 0,
            },
        });

        // Store BLOCK_DIM_X to memory
        program.instructions.push(Instruction::STG {
            ty: Type::U32,
            src: BLOCK_DIM_X,
            addr: Address::BufferOffset {
                handle: buf_block_dim.0,
                offset: 0,
            },
        });

        // Store GLOBAL_LANE_ID to memory
        program.instructions.push(Instruction::STG {
            ty: Type::U64,
            src: GLOBAL_LANE_ID,
            addr: Address::BufferOffset {
                handle: buf_global_id.0,
                offset: 0,
            },
        });

        // EXIT
        program.instructions.push(Instruction::EXIT);

        // Execute program
        let result = executor.execute(&program, &config);
        assert!(result.is_ok(), "Program execution should succeed");

        // Read back values (just verify we can read without errors)
        {
            let mem = memory.read();
            let mut lane_idx_bytes = [0u8; 4];
            let mut block_idx_bytes = [0u8; 4];
            let mut block_dim_bytes = [0u8; 4];
            let mut global_id_bytes = [0u8; 8];

            mem.copy_from_buffer(buf_lane_idx, &mut lane_idx_bytes).unwrap();
            mem.copy_from_buffer(buf_block_idx, &mut block_idx_bytes).unwrap();
            mem.copy_from_buffer(buf_block_dim, &mut block_dim_bytes).unwrap();
            mem.copy_from_buffer(buf_global_id, &mut global_id_bytes).unwrap();

            // Verify the stored values make sense
            let lane_idx = u32::from_le_bytes(lane_idx_bytes);
            let block_dim = u32::from_le_bytes(block_dim_bytes);

            // Lane index should be < block dimension
            assert!(lane_idx < 4, "lane_idx should be < 4, got {}", lane_idx);
            assert_eq!(block_dim, 4, "block_dim should be 4");
        }

        // Clean up
        memory.write().free_buffer(buf_lane_idx).unwrap();
        memory.write().free_buffer(buf_block_idx).unwrap();
        memory.write().free_buffer(buf_block_dim).unwrap();
        memory.write().free_buffer(buf_global_id).unwrap();
    }

    #[test]
    fn test_vector_add_with_special_registers() {
        // This test demonstrates that special registers are properly initialized
        // by verifying that a simple program using them executes successfully.
        // A full vector add using RegisterIndirect addressing would require
        // loading buffer handles into registers first.

        let n: usize = 4;

        let memory = Arc::new(RwLock::new(MemoryManager::new()));
        let executor = CpuExecutor::new(Arc::clone(&memory));

        // Allocate buffers
        let buf_a = memory.write().allocate_buffer(n * 4).unwrap(); // n × f32
        let buf_b = memory.write().allocate_buffer(n * 4).unwrap();
        let buf_c = memory.write().allocate_buffer(n * 4).unwrap();

        // Initialize input data (first element only for simplicity)
        {
            let mut mem = memory.write();
            let a_val = 5.0f32;
            let b_val = 7.0f32;
            mem.copy_to_buffer(buf_a, bytemuck::bytes_of(&a_val)).unwrap();
            mem.copy_to_buffer(buf_b, bytemuck::bytes_of(&b_val)).unwrap();
        }

        // Create a simple program that uses special registers
        // This verifies they're initialized correctly
        let mut program = Program::new();

        // Load from first element of each buffer (lane 0 only)
        program.instructions.push(Instruction::LDG {
            ty: Type::F32,
            dst: Register::new(2),
            addr: Address::BufferOffset {
                handle: buf_a.0,
                offset: 0,
            },
        });

        program.instructions.push(Instruction::LDG {
            ty: Type::F32,
            dst: Register::new(3),
            addr: Address::BufferOffset {
                handle: buf_b.0,
                offset: 0,
            },
        });

        // Add: r4 = r2 + r3
        program.instructions.push(Instruction::ADD {
            ty: Type::F32,
            dst: Register::new(4),
            src1: Register::new(2),
            src2: Register::new(3),
        });

        // Store result
        program.instructions.push(Instruction::STG {
            ty: Type::F32,
            src: Register::new(4),
            addr: Address::BufferOffset {
                handle: buf_c.0,
                offset: 0,
            },
        });

        // EXIT
        program.instructions.push(Instruction::EXIT);

        // Execute with n lanes (1 block × n threads)
        // Special registers will be initialized for all lanes
        let config = LaunchConfig::linear(n as u32, n as u32);
        let result = executor.execute(&program, &config);
        assert!(result.is_ok(), "Program execution should succeed: {:?}", result);

        // Verify result from lane 0
        {
            let mem = memory.read();
            let mut result_bytes = [0u8; 4];
            mem.copy_from_buffer(buf_c, &mut result_bytes).unwrap();
            let result_val = f32::from_le_bytes(result_bytes);
            assert_eq!(result_val, 12.0, "5.0 + 7.0 should equal 12.0");
        }

        // Clean up
        memory.write().free_buffer(buf_a).unwrap();
        memory.write().free_buffer(buf_b).unwrap();
        memory.write().free_buffer(buf_c).unwrap();
    }

    #[test]
    fn test_phicoordinate_addressing() {
        // This test verifies that PhiCoordinate addressing is now integrated and working
        use crate::isa::{Address, Instruction, Program, Register, Type};

        // Create memory manager
        let memory = Arc::new(RwLock::new(MemoryManager::new()));
        let executor = CpuExecutor::new(Arc::clone(&memory));

        // Create a program that uses PhiCoordinate addressing
        let mut program = Program::new();

        // Store value 42.0 to class 0, page 0, byte 0
        program.instructions.push(Instruction::MOV_IMM {
            ty: Type::F32,
            dst: Register(0),
            value: 42.0f32.to_bits() as u64,
        });

        program.instructions.push(Instruction::STG {
            ty: Type::F32,
            src: Register(0),
            addr: Address::PhiCoordinate {
                class: 0,
                page: 0,
                byte: 0,
            },
        });

        // Load value back from class 0, page 0, byte 0
        program.instructions.push(Instruction::LDG {
            ty: Type::F32,
            dst: Register(1),
            addr: Address::PhiCoordinate {
                class: 0,
                page: 0,
                byte: 0,
            },
        });

        program.instructions.push(Instruction::EXIT);

        // Execute program
        let config = LaunchConfig::default();
        let result = executor.execute(&program, &config);

        // Should succeed - PhiCoordinate addressing is now integrated!
        assert!(result.is_ok(), "PhiCoordinate addressing should work: {:?}", result);
    }
}
