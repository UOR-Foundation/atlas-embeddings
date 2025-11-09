//! Execution state management shared across all backends
//!
//! Provides lane-based execution state structures used by CPU, GPU, TPU, and FPGA backends.
//!
//! # Architecture
//!
//! - `LaneState`: Per-thread execution state (registers, PC, call stack, Atlas state)
//! - `ExecutionState`: Global state managing multiple lanes, memory, and context

use crate::backend::ExecutionContext;
use crate::backends::common::memory::MemoryStorage;
use crate::backends::common::RegisterFile;
use parking_lot::RwLock;
use std::collections::HashMap;
use std::sync::Arc;

// ================================================================================================
// Lane State
// ================================================================================================

/// Per-lane execution state
///
/// Each lane (thread) maintains its own register file and program counter.
/// This structure is used across all backend implementations.
///
/// # Fields
///
/// - `registers`: 256 typed registers + 16 predicates
/// - `pc`: Program counter (instruction index)
/// - `active`: Whether execution should continue
/// - `call_stack`: Return addresses for CALL/RET instructions
/// - `current_class`: Current Atlas resonance class [0, 96)
/// - `phase_counter`: Atlas phase synchronization counter [0, 768)
pub struct LaneState {
    /// Register file (256 registers + 16 predicates)
    pub registers: RegisterFile,

    /// Program counter
    pub pc: usize,

    /// Whether execution should continue
    pub active: bool,

    /// Call stack for CALL/RET instructions (stores return addresses)
    pub call_stack: Vec<usize>,

    /// Current resonance class (for Atlas operations)
    pub current_class: u8,

    /// Phase counter (for Atlas synchronization)
    pub phase_counter: u32,
}

impl LaneState {
    /// Create a new lane state with default values
    pub fn new() -> Self {
        Self {
            registers: RegisterFile::new(),
            pc: 0,
            active: true,
            call_stack: Vec::new(),
            current_class: 0, // Start at identity class
            phase_counter: 0, // Start at phase 0
        }
    }
}

impl Default for LaneState {
    fn default() -> Self {
        Self::new()
    }
}

// ================================================================================================
// Lane Execution State (Per-Lane)
// ================================================================================================

/// Per-lane execution state (thread-owned)
///
/// Each thread owns its own `LaneExecutionState` during parallel execution.
/// This structure contains all state that is exclusively modified by a single lane.
///
/// # Fields
///
/// - `lane`: Register file, PC, call stack, Atlas state
/// - `context`: Execution context with this lane's indices
///
/// # Thread Safety
///
/// This structure is NOT thread-safe and should not be shared between threads.
/// Each thread gets its own `LaneExecutionState` during parallel execution.
pub struct LaneExecutionState {
    /// Lane-specific state (registers, PC, etc.)
    pub lane: LaneState,

    /// Execution context for this specific lane
    pub context: ExecutionContext,
}

impl LaneExecutionState {
    /// Create a new lane execution state
    pub fn new(context: ExecutionContext) -> Self {
        Self {
            lane: LaneState::new(),
            context,
        }
    }
}

// ================================================================================================
// Shared Execution State (Thread-Safe)
// ================================================================================================

/// Shared execution state (thread-safe)
///
/// Contains all state that is shared across multiple lanes during parallel execution.
/// All fields use thread-safe synchronization primitives (Arc, RwLock).
///
/// # Fields
///
/// - `memory`: Shared memory manager (already thread-safe)
/// - `labels`: Read-only label mapping (wrapped in Arc for efficient sharing)
/// - `resonance_accumulator`: Mutable resonance tracking (protected by RwLock)
///
/// # Thread Safety
///
/// All fields are thread-safe:
/// - `memory`: Uses `Arc<RwLock<M>>` for concurrent access
/// - `labels`: Uses `Arc<HashMap>` for lock-free reads (immutable)
/// - `resonance_accumulator`: Uses `Arc<RwLock<HashMap>>` for thread-safe updates
pub struct SharedExecutionState<M: MemoryStorage> {
    /// Shared memory manager
    pub memory: Arc<RwLock<M>>,

    /// Label to instruction index mapping (read-only, lock-free)
    pub labels: Arc<HashMap<String, usize>>,

    /// Resonance accumulator: tracks accumulated values per class (thread-safe)
    /// Used by ResAccum instruction for Atlas resonance tracking
    pub resonance_accumulator: Arc<RwLock<HashMap<u8, f64>>>,
}

impl<M: MemoryStorage> SharedExecutionState<M> {
    /// Create a new shared execution state
    pub fn new(memory: Arc<RwLock<M>>, labels: HashMap<String, usize>) -> Self {
        Self {
            memory,
            labels: Arc::new(labels),
            resonance_accumulator: Arc::new(RwLock::new(HashMap::new())),
        }
    }
}

// ================================================================================================
// Execution State (Combined)
// ================================================================================================

/// Full execution state for a program (Phase 2: Refactored for Parallelism)
///
/// Combines per-lane states with shared state to enable fine-grained parallelism.
/// This architecture allows Rayon to parallelize lane execution without shared mutable state.
///
/// # Type Parameter
///
/// - `M`: Memory storage backend (e.g., CPU Vec<u8>, GPU device memory)
///
/// # Architecture
///
/// - `lane_states`: Vector of per-lane states (thread-owned, one per lane)
/// - `shared`: Shared state (thread-safe, accessed by all lanes)
///
/// # Parallelization Benefits
///
/// This split architecture enables:
/// - Fine-grained lane-level parallelism (each thread owns one `LaneExecutionState`)
/// - No shared mutable state between lanes (Rayon can prove independence)
/// - Thread-safe access to shared resources (memory, labels, resonance_accumulator)
pub struct ExecutionState<M: MemoryStorage> {
    /// Lane execution states (one per thread in block)
    pub lane_states: Vec<LaneExecutionState>,

    /// Shared execution state (thread-safe)
    pub shared: SharedExecutionState<M>,
}

impl<M: MemoryStorage> ExecutionState<M> {
    /// Create a new execution state
    ///
    /// # Arguments
    ///
    /// * `num_lanes` - Number of lanes (threads) per block
    /// * `memory` - Shared memory manager
    /// * `context` - Base execution context (will be cloned per lane with updated indices)
    /// * `labels` - Label to instruction index mapping
    pub fn new(
        num_lanes: usize,
        memory: Arc<RwLock<M>>,
        context: ExecutionContext,
        labels: HashMap<String, usize>,
    ) -> Self {
        // Create lane-specific contexts (each lane gets its own context with correct indices)
        let lane_states = (0..num_lanes).map(|_| LaneExecutionState::new(context)).collect();

        // Create shared state (thread-safe)
        let shared = SharedExecutionState::new(memory, labels);

        Self { lane_states, shared }
    }

    /// Get current lane (immutable) - for backward compatibility
    pub fn current_lane(&self) -> &LaneState {
        // For single-lane ExecutionStates (parallel execution), always use index 0
        // For multi-lane ExecutionStates (sequential execution), use first lane's context
        let idx = if self.lane_states.len() == 1 {
            0
        } else {
            self.lane_states[0].context.lane_idx.0 as usize
        };
        &self.lane_states[idx].lane
    }

    /// Get current lane (mutable) - for backward compatibility
    pub fn current_lane_mut(&mut self) -> &mut LaneState {
        // For single-lane ExecutionStates (parallel execution), always use index 0
        // For multi-lane ExecutionStates (sequential execution), use first lane's context
        let idx = if self.lane_states.len() == 1 {
            0
        } else {
            self.lane_states[0].context.lane_idx.0 as usize
        };
        &mut self.lane_states[idx].lane
    }

    /// Get specific lane by index (immutable)
    pub fn lane(&self, idx: usize) -> Option<&LaneState> {
        self.lane_states.get(idx).map(|ls| &ls.lane)
    }

    /// Get specific lane by index (mutable)
    pub fn lane_mut(&mut self, idx: usize) -> Option<&mut LaneState> {
        self.lane_states.get_mut(idx).map(|ls| &mut ls.lane)
    }

    /// Get number of lanes
    pub fn num_lanes(&self) -> usize {
        self.lane_states.len()
    }

    /// Reset all lane state (for re-execution)
    pub fn reset_lanes(&mut self) {
        for lane_state in &mut self.lane_states {
            lane_state.lane.registers.reset();
            lane_state.lane.pc = 0;
            lane_state.lane.active = true;
            lane_state.lane.call_stack.clear();
            lane_state.lane.current_class = 0;
            lane_state.lane.phase_counter = 0;
        }
        self.shared.resonance_accumulator.write().clear();
    }

    // ============================================================================================
    // Backward Compatibility Accessors
    // ============================================================================================

    /// Access memory (backward compatibility)
    pub fn memory(&self) -> &Arc<RwLock<M>> {
        &self.shared.memory
    }

    /// Access labels (backward compatibility)
    pub fn labels(&self) -> &HashMap<String, usize> {
        &self.shared.labels
    }

    /// Access context from first lane (backward compatibility)
    pub fn context(&self) -> &ExecutionContext {
        &self.lane_states[0].context
    }

    /// Access lanes directly (backward compatibility) - returns reference to lane states
    pub fn lanes(&self) -> Vec<&LaneState> {
        self.lane_states.iter().map(|ls| &ls.lane).collect()
    }

    /// Access lanes mutably (backward compatibility)
    pub fn lanes_mut(&mut self) -> Vec<&mut LaneState> {
        self.lane_states.iter_mut().map(|ls| &mut ls.lane).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Mock memory storage for testing
    struct MockStorage;
    impl MemoryStorage for MockStorage {
        fn allocate_buffer(&mut self, _size: usize) -> crate::error::Result<crate::backend::BufferHandle> {
            Ok(crate::backend::BufferHandle::new(0))
        }
        fn free_buffer(&mut self, _handle: crate::backend::BufferHandle) -> crate::error::Result<()> {
            Ok(())
        }
        fn copy_to_buffer(&mut self, _handle: crate::backend::BufferHandle, _data: &[u8]) -> crate::error::Result<()> {
            Ok(())
        }
        fn copy_from_buffer(
            &self,
            _handle: crate::backend::BufferHandle,
            _data: &mut [u8],
        ) -> crate::error::Result<()> {
            Ok(())
        }
        fn buffer_size(&self, _handle: crate::backend::BufferHandle) -> crate::error::Result<usize> {
            Ok(0)
        }
        fn allocate_pool(&mut self, _size: usize) -> crate::error::Result<crate::backend::PoolHandle> {
            Ok(crate::backend::PoolHandle::new(0))
        }
        fn free_pool(&mut self, _handle: crate::backend::PoolHandle) -> crate::error::Result<()> {
            Ok(())
        }
        fn copy_to_pool(
            &mut self,
            _handle: crate::backend::PoolHandle,
            _offset: usize,
            _data: &[u8],
        ) -> crate::error::Result<()> {
            Ok(())
        }
        fn copy_from_pool(
            &self,
            _handle: crate::backend::PoolHandle,
            _offset: usize,
            _data: &mut [u8],
        ) -> crate::error::Result<()> {
            Ok(())
        }
        fn pool_size(&self, _handle: crate::backend::PoolHandle) -> crate::error::Result<usize> {
            Ok(0)
        }
    }

    #[test]
    fn test_lane_state_creation() {
        let lane = LaneState::new();
        assert_eq!(lane.pc, 0);
        assert!(lane.active);
        assert!(lane.call_stack.is_empty());
        assert_eq!(lane.current_class, 0);
        assert_eq!(lane.phase_counter, 0);
    }

    #[test]
    fn test_execution_state_creation() {
        let memory = Arc::new(RwLock::new(MockStorage));
        use crate::backend::{BlockDim, GridDim};
        let context = ExecutionContext::new((0, 0, 0), (0, 0, 0), GridDim::new(1, 1, 1), BlockDim::new(4, 1, 1));
        let labels = HashMap::new();

        let state = ExecutionState::new(4, memory, context, labels);
        assert_eq!(state.num_lanes(), 4);
        assert!(state.shared.resonance_accumulator.read().is_empty());
    }

    #[test]
    fn test_current_lane_access() {
        let memory = Arc::new(RwLock::new(MockStorage));
        use crate::backend::{BlockDim, GridDim};
        let context = ExecutionContext::new((0, 0, 0), (0, 0, 0), GridDim::new(1, 1, 1), BlockDim::new(2, 1, 1));
        let labels = HashMap::new();

        let mut state = ExecutionState::new(2, memory, context, labels);

        // Access current lane
        let lane = state.current_lane();
        assert_eq!(lane.pc, 0);

        // Modify current lane
        state.current_lane_mut().pc = 42;
        assert_eq!(state.current_lane().pc, 42);
    }

    #[test]
    fn test_reset_lanes() {
        let memory = Arc::new(RwLock::new(MockStorage));
        use crate::backend::{BlockDim, GridDim};
        let context = ExecutionContext::new((0, 0, 0), (0, 0, 0), GridDim::new(1, 1, 1), BlockDim::new(2, 1, 1));
        let labels = HashMap::new();

        let mut state = ExecutionState::new(2, memory, context, labels);

        // Modify state (using new structure)
        state.lane_states[0].lane.pc = 10;
        state.lane_states[0].lane.active = false;
        state.lane_states[0].lane.current_class = 42;
        state.shared.resonance_accumulator.write().insert(5, 1.5);

        // Reset
        state.reset_lanes();

        // Verify reset (using new structure)
        assert_eq!(state.lane_states[0].lane.pc, 0);
        assert!(state.lane_states[0].lane.active);
        assert_eq!(state.lane_states[0].lane.current_class, 0);
        assert!(state.shared.resonance_accumulator.read().is_empty());
    }
}
