//! Executor trait for instruction-level execution
//!
//! This trait defines the interface for backend-specific instruction execution.
//! While the `Backend` trait provides the public API, this trait enables backends
//! to share instruction dispatch logic while customizing backend-specific operations.

use crate::backends::common::ExecutionState;
use crate::error::Result;
use crate::isa::{Instruction, MemoryScope};

/// Executor trait for backend-specific instruction execution
///
/// This trait encapsulates the complete instruction execution logic for a backend.
/// Backends implement this trait to provide:
///
/// - **Complete execution** via `execute()` method
/// - **Single instruction execution** via `execute_instruction()`
/// - **Backend-specific memory operations** (LDG, STG, LDS, STS)
/// - **Backend-specific synchronization** (BarSync, MemFence)
///
/// All non-backend-specific instructions (arithmetic, bitwise, math, Atlas ops)
/// can use the shared `instruction_ops` implementations.
///
/// # Architecture
///
/// ```text
/// ┌─────────────────────────────────────────┐
/// │          Backend Trait (Public)          │
/// │  - execute_program()  ───────────┐       │
/// │  - allocate_buffer()             │       │
/// │  - allocate_pool()               │       │
/// └──────────────────────────────────┼───────┘
///                                    │
///                                    │ delegates to
///                                    ▼
/// ┌─────────────────────────────────────────┐
/// │      Executor Trait (Execution)          │
/// │  - execute()  (main execution loop)      │
/// │  - execute_instruction()                 │
/// │  - execute_barrier_sync()                │
/// │  - execute_memory_fence()                │
/// │  - execute_load_global()                 │
/// │  - execute_store_global()                │
/// └──────────────────┬──────────────────────┘
///                    │
///      ┌─────────────┼─────────────┐
///      ▼             ▼             ▼
/// ┌────────┐   ┌────────┐   ┌────────┐
/// │  CPU   │   │  GPU   │   │  TPU   │
/// │Executor│   │Executor│   │Executor│
/// └────────┘   └────────┘   └────────┘
/// ```
///
/// # Example Implementation
///
/// ```text
/// use hologram_backends::backends::common::{Executor, ExecutionState};
/// use hologram_backends::isa::{Instruction, Program};
/// use hologram_backends::backend::LaunchConfig;
///
/// pub struct CpuExecutor {
///     memory: Arc<RwLock<MemoryManager>>,
/// }
///
/// impl Executor<MemoryManager> for CpuExecutor {
///     fn execute(
///         &mut self,
///         program: &Program,
///         config: &LaunchConfig,
///     ) -> Result<()> {
///         // Create execution state
///         let mut state = ExecutionState::new(...);
///
///         // Main execution loop
///         while state.current_lane().active && state.current_lane().pc < program.instructions.len() {
///             let instruction = &program.instructions[state.current_lane().pc];
///             self.execute_instruction(&mut state, instruction)?;
///             state.current_lane_mut().pc += 1;
///         }
///
///         Ok(())
///     }
///
///     fn execute_instruction(
///         &mut self,
///         state: &mut ExecutionState<MemoryManager>,
///         instruction: &Instruction,
///     ) -> Result<()> {
///         match instruction {
///             // Memory operations (backend-specific)
///             Instruction::LDG { .. } => self.execute_ldg(state, ...),
///
///             // Synchronization (backend-specific)
///             Instruction::BarSync { id } => self.execute_barrier_sync(state, *id),
///
///             // Arithmetic (shared)
///             Instruction::ADD { .. } => instruction_ops::execute_add(state, ...),
///
///             // ... etc
///         }
///     }
///
///     // Backend-specific implementations
///     fn execute_barrier_sync(&mut self, state: &mut ExecutionState<MemoryManager>, barrier_id: u8) -> Result<()> {
///         // CPU-specific implementation
///         Ok(())
///     }
///
///     // ... other methods
/// }
/// ```
pub trait Executor<M: super::MemoryStorage> {
    // ============================================================================================
    // Program Execution
    // ============================================================================================

    /// Execute a program with the given launch configuration
    ///
    /// This is the main entry point for program execution. Backends implement
    /// their complete execution strategy here (sequential, parallel, etc.).
    ///
    /// # Arguments
    ///
    /// * `program` - The program to execute
    /// * `config` - Launch configuration (grid/block dimensions)
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` on successful execution, or an error if execution fails.
    fn execute(&self, program: &crate::isa::Program, config: &crate::backend::LaunchConfig)
        -> crate::error::Result<()>;

    /// Execute a single instruction
    ///
    /// Backends implement their instruction dispatch logic here, delegating to:
    /// - Shared `instruction_ops` for arithmetic, bitwise, math operations
    /// - Shared `atlas_ops` for Atlas-specific operations
    /// - Backend-specific methods for memory and synchronization operations
    ///
    /// # Arguments
    ///
    /// * `state` - Current execution state
    /// * `instruction` - The instruction to execute
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` on successful execution, or an error if the instruction fails.
    fn execute_instruction(
        &self,
        state: &mut super::ExecutionState<M>,
        instruction: &crate::isa::Instruction,
    ) -> crate::error::Result<()>;
    // ============================================================================================
    // Synchronization Operations
    // ============================================================================================

    /// Execute barrier synchronization
    ///
    /// Synchronizes all lanes/threads in a barrier group. All lanes must reach
    /// the barrier before any can proceed.
    ///
    /// # Arguments
    ///
    /// * `state` - Execution state
    /// * `barrier_id` - Barrier identifier (0-255)
    ///
    /// # Backend-Specific Behavior
    ///
    /// - **CPU (Single-threaded)**: No-op
    /// - **CPU (Multi-threaded)**: Uses `std::sync::Barrier`
    /// - **GPU**: Uses `__syncthreads()` or equivalent
    /// - **TPU**: Uses hardware synchronization primitives
    fn execute_barrier_sync(&self, state: &mut ExecutionState<M>, barrier_id: u8) -> Result<()>;

    /// Execute memory fence
    ///
    /// Ensures memory operations are visible according to the specified scope.
    ///
    /// # Arguments
    ///
    /// * `state` - Execution state
    /// * `scope` - Memory scope (Thread, Block, Device, System)
    ///
    /// # Backend-Specific Behavior
    ///
    /// - **CPU**: Uses `std::sync::atomic::fence()`
    /// - **GPU**: Uses `__threadfence_block()`, `__threadfence()`, `__threadfence_system()`
    /// - **TPU**: Uses memory barrier instructions
    fn execute_memory_fence(&self, state: &mut ExecutionState<M>, scope: MemoryScope) -> Result<()>;

    // ============================================================================================
    // Memory Operations (Optional - Can provide default implementations)
    // ============================================================================================

    // Note: Memory operations (LDG, STG, LDS, STS) are backend-specific and
    // implemented directly in the backend executor. They're not part of this
    // trait because they access backend-specific memory management.
}

/// Dispatch instruction to appropriate handler
///
/// This function provides common instruction dispatch logic that all backends
/// can use. It routes instructions to either:
/// - Shared `instruction_ops` functions (arithmetic, bitwise, math, etc.)
/// - Backend-specific `Executor` trait methods (synchronization)
/// - Backend-specific memory operations (handled by caller)
///
/// # Usage
///
/// ```text
/// fn execute_instruction(state: &mut ExecutionState, instruction: &Instruction) -> Result<()> {
///     match instruction {
///         // Memory operations (backend-specific)
///         Instruction::LDG { .. } => execute_ldg(state, ...),
///         Instruction::STG { .. } => execute_stg(state, ...),
///
///         // Synchronization (via Executor trait)
///         Instruction::BarSync { id } => CpuExecutor::execute_barrier_sync(state, *id),
///         Instruction::MemFence { scope } => CpuExecutor::execute_memory_fence(state, *scope),
///
///         // All other instructions (shared via instruction_ops)
///         _ => dispatch_common_instruction(state, instruction),
///     }
/// }
/// ```
pub fn dispatch_common_instruction<M: super::MemoryStorage>(
    state: &mut ExecutionState<M>,
    instruction: &Instruction,
) -> Result<()> {
    use crate::backends::common::{atlas_ops, instruction_ops};

    match instruction {
        // Data Movement
        Instruction::MOV { ty, dst, src } => instruction_ops::execute_mov(state, *ty, *dst, *src),
        Instruction::CVT {
            src_ty,
            dst_ty,
            dst,
            src,
        } => instruction_ops::execute_cvt(state, *src_ty, *dst_ty, *dst, *src),
        Instruction::MOV_IMM { ty, dst, value } => instruction_ops::execute_mov_imm(state, *ty, *dst, *value),

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

        // Control Flow (could be moved to instruction_ops in the future)
        Instruction::BRA { .. }
        | Instruction::CALL { .. }
        | Instruction::RET
        | Instruction::LOOP { .. }
        | Instruction::EXIT => {
            // These are currently backend-specific but could be shared
            use crate::error::BackendError;
            Err(BackendError::execution_error(
                "Control flow instructions must be handled by backend executor".to_string(),
            ))
        }

        // Atlas-Specific
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

        // Memory operations (LDG, STG, LDS, STS) and synchronization (BarSync, MemFence)
        // must be handled by the backend executor
        Instruction::LDG { .. }
        | Instruction::STG { .. }
        | Instruction::LDS { .. }
        | Instruction::STS { .. }
        | Instruction::BarSync { .. }
        | Instruction::MemFence { .. } => {
            use crate::error::BackendError;
            Err(BackendError::execution_error(
                "Memory and synchronization instructions must be handled by backend executor".to_string(),
            ))
        }
    }
}
