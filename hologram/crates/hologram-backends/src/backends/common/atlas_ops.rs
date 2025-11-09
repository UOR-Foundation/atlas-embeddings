//! Atlas-specific instruction implementations shared across backends
//!
//! All Atlas-specific operations delegate to `atlas-core` for canonical implementations:
//! - ClsGet: Get current resonance class
//! - MIRROR: Compute mirror class transformation
//! - PhaseGet/PhaseAdv: Phase counter operations
//! - UnityTest: Check if class is in unity set
//! - NbrCount/NbrGet: Atlas graph neighbor queries
//! - ResAccum: Resonance accumulation
//! - BoundMap: Φ-coordinate to linear address mapping
//!
//! These implementations are ~95% shareable across all backends (CPU, GPU, TPU, FPGA)
//! because they all delegate to atlas-core functions. Only register access differs.

use crate::backends::common::execution_state::ExecutionState;
use crate::backends::common::memory::MemoryStorage;
use crate::error::{BackendError, Result};
use crate::isa::{Predicate, Register};
use atlas_core::{
    get_mirror_pair, is_unity, PhiCoordinate, ResonanceClass, PHASE_MODULUS, RESONANCE_CLASSES, TOTAL_ELEMENTS,
};

// ================================================================================================
// Atlas Class Operations
// ================================================================================================

/// Get current resonance class
///
/// Returns the current Atlas resonance class [0, 96) from lane state.
///
/// # Instruction
///
/// `ClsGet dst`
///
/// # Implementation
///
/// Reads `current_class` from lane state and writes to destination register.
pub fn execute_cls_get<M: MemoryStorage>(state: &mut ExecutionState<M>, dst: Register) -> Result<()> {
    let lane = state.current_lane_mut();
    lane.registers.write_u8(dst, lane.current_class)?;
    Ok(())
}

/// Compute mirror class transformation
///
/// Uses atlas-core's `get_mirror_pair()` to compute the mirror transformation
/// of a resonance class in the Atlas graph.
///
/// # Instruction
///
/// `MIRROR dst, src`
///
/// # Implementation
///
/// ```text
/// class = registers[src]
/// mirrored_class = get_mirror_pair(class)  // atlas-core
/// registers[dst] = mirrored_class
/// ```
///
/// Mirror pairs are defined by the Atlas graph structure and computed by atlas-embeddings.
pub fn execute_mirror<M: MemoryStorage>(state: &mut ExecutionState<M>, dst: Register, src: Register) -> Result<()> {
    let lane = state.current_lane_mut();
    let class = lane.registers.read_u8(src)?;

    // Use atlas-core's get_mirror_pair function
    let mirrored_class = get_mirror_pair(class);

    lane.registers.write_u8(dst, mirrored_class)?;
    Ok(())
}

// ================================================================================================
// Phase Operations
// ================================================================================================

/// Get current phase counter
///
/// Returns the current phase counter [0, 768) from lane state.
///
/// # Instruction
///
/// `PhaseGet dst`
///
/// # Implementation
///
/// Reads `phase_counter` from lane state and writes to destination register.
pub fn execute_phase_get<M: MemoryStorage>(state: &mut ExecutionState<M>, dst: Register) -> Result<()> {
    let lane = state.current_lane_mut();
    lane.registers.write_u32(dst, lane.phase_counter)?;
    Ok(())
}

/// Advance phase counter
///
/// Advances the phase counter by delta with modulo PHASE_MODULUS (768).
///
/// # Instruction
///
/// `PhaseAdv delta`
///
/// # Implementation
///
/// ```text
/// phase_counter = (phase_counter + delta) % PHASE_MODULUS
/// ```
///
/// PHASE_MODULUS = 768 = 8 × 96 (8 complete cycles through all 96 resonance classes)
pub fn execute_phase_adv<M: MemoryStorage>(state: &mut ExecutionState<M>, delta: u16) -> Result<()> {
    let lane = state.current_lane_mut();
    lane.phase_counter = (lane.phase_counter + delta as u32) % PHASE_MODULUS;
    Ok(())
}

// ================================================================================================
// Unity Operations
// ================================================================================================

/// Test if current class is in unity set
///
/// Uses atlas-core's `is_unity()` to check if the current resonance class
/// is in the unity set (special classes with identity properties).
///
/// # Instruction
///
/// `UnityTest dst, epsilon`
///
/// # Implementation
///
/// ```text
/// is_unity_class = is_unity(current_class)  // atlas-core
/// predicates[dst] = is_unity_class
/// ```
///
/// The epsilon parameter is currently unused but reserved for future threshold testing.
pub fn execute_unity_test<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    dst: Predicate,
    _epsilon: f64,
) -> Result<()> {
    let lane = state.current_lane_mut();
    let is_unity_class = is_unity(lane.current_class);
    lane.registers.write_predicate(dst, is_unity_class)?;
    Ok(())
}

// ================================================================================================
// Neighbor Operations
// ================================================================================================

/// Get neighbor count for resonance class
///
/// Uses atlas-core's `ResonanceClass::degree()` to query the Atlas graph
/// for the number of neighbors of the specified class.
///
/// # Instruction
///
/// `NbrCount class, dst`
///
/// # Implementation
///
/// ```text
/// class_id = registers[class]
/// resonance_class = ResonanceClass::new(class_id)  // atlas-core
/// neighbor_count = resonance_class.degree()        // query Atlas graph
/// registers[dst] = neighbor_count
/// ```
pub fn execute_nbr_count<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    class: Register,
    dst: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    let class_id = lane.registers.read_u8(class)?;

    // Create ResonanceClass and query degree from Atlas graph
    let resonance_class =
        ResonanceClass::new(class_id).map_err(|e| BackendError::execution_error(format!("Invalid class ID: {}", e)))?;

    let neighbor_count = resonance_class.degree() as u32;
    lane.registers.write_u32(dst, neighbor_count)?;
    Ok(())
}

/// Get neighbor by index
///
/// Uses atlas-core's `ResonanceClass::neighbors()` to query the Atlas graph
/// for the neighbors of the specified class and return the neighbor at index.
///
/// # Instruction
///
/// `NbrGet class, index, dst`
///
/// # Implementation
///
/// ```text
/// class_id = registers[class]
/// resonance_class = ResonanceClass::new(class_id)  // atlas-core
/// neighbors = resonance_class.neighbors()          // query Atlas graph
/// neighbor_id = neighbors[index] (or 0 if out of bounds)
/// registers[dst] = neighbor_id
/// ```
pub fn execute_nbr_get<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    class: Register,
    index: u8,
    dst: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    let class_id = lane.registers.read_u8(class)?;

    // Create ResonanceClass and query neighbors from Atlas graph
    let resonance_class =
        ResonanceClass::new(class_id).map_err(|e| BackendError::execution_error(format!("Invalid class ID: {}", e)))?;

    let neighbors = resonance_class.neighbors();

    // Return the neighbor at the specified index, or class 0 if out of bounds
    let neighbor_id = if (index as usize) < neighbors.len() {
        neighbors[index as usize].id()
    } else {
        0 // Default to identity class if index out of bounds
    };

    lane.registers.write_u8(dst, neighbor_id)?;
    Ok(())
}

// ================================================================================================
// Resonance Operations
// ================================================================================================

/// Accumulate resonance value for class
///
/// Accumulates a value into the global resonance accumulator for the specified class.
/// The accumulator tracks resonance values across all lanes for Atlas computations.
///
/// # Instruction
///
/// `ResAccum class, value`
///
/// # Implementation
///
/// ```text
/// class_id = registers[class]
/// value_f64 = registers[value]
/// resonance_accumulator[class_id] += value_f64
/// ```
///
/// The resonance accumulator is shared across all lanes in the execution state.
pub fn execute_res_accum<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    class: Register,
    value: Register,
) -> Result<()> {
    let lane = state.current_lane();
    let class_id = lane.registers.read_u8(class)?;
    let value_f64 = lane.registers.read_f64(value)?;

    // Add to the resonance accumulator for this class (thread-safe)
    let mut accum = state.shared.resonance_accumulator.write();
    let entry = accum.entry(class_id).or_insert(0.0);
    *entry += value_f64;

    Ok(())
}

// ================================================================================================
// Boundary Operations
// ================================================================================================

/// Map Φ-coordinates to linear address
///
/// Converts Atlas Φ-coordinates (class, page, byte) to a linear memory address
/// using atlas-core's categorical × cellular structure.
///
/// # Instruction
///
/// `BoundMap class, page, byte, dst`
///
/// # Implementation
///
/// ```text
/// class = registers[class]  // [0, 96) resonance class
/// page = registers[page]    // [0, 48) page within class
/// byte = registers[byte]    // [0, 256) byte within page
///
/// // Validate using atlas-core
/// validate class < RESONANCE_CLASSES (96)
/// phi = PhiCoordinate::new(page, byte)  // validates page < 48
///
/// // Calculate linear address
/// page_byte_offset = phi.linear_index()  // page × 256 + byte
/// class_offset = class × TOTAL_ELEMENTS  // class × 12,288
/// linear_addr = class_offset + page_byte_offset
///
/// registers[dst] = linear_addr
/// ```
///
/// This maps Atlas's 96 × 48 × 256 categorical structure to linear memory.
pub fn execute_bound_map<M: MemoryStorage>(
    state: &mut ExecutionState<M>,
    class: Register,
    page: Register,
    byte: Register,
    dst: Register,
) -> Result<()> {
    let lane = state.current_lane_mut();
    let class_val = lane.registers.read_u8(class)?;
    let page_val = lane.registers.read_u8(page)?;
    let byte_val = lane.registers.read_u8(byte)?;

    // Validate class is in valid range using atlas-core constant
    if class_val >= RESONANCE_CLASSES as u8 {
        return Err(BackendError::execution_error(format!(
            "Invalid class ID {} for BoundMap (must be < {})",
            class_val, RESONANCE_CLASSES
        )));
    }

    // Use atlas-core's PhiCoordinate for validation and linear indexing
    let phi = PhiCoordinate::new(page_val, byte_val)
        .map_err(|e| BackendError::execution_error(format!("Invalid Φ-coordinate for BoundMap: {}", e)))?;

    // Get linear offset within class using atlas-core's method
    let page_byte_offset = phi.linear_index() as u64;

    // Calculate full linear address: class_offset + linear_index
    // Each class has TOTAL_ELEMENTS (12,288) bytes
    let class_offset = (class_val as u64) * (TOTAL_ELEMENTS as u64);
    let linear_addr = class_offset + page_byte_offset;

    lane.registers.write_u64(dst, linear_addr)?;

    Ok(())
}

// ================================================================================================
// Tests
// ================================================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::ExecutionContext;
    use crate::backend::{BufferHandle, PoolHandle};
    use crate::backends::common::memory::MemoryStorage;
    use parking_lot::RwLock;
    use std::collections::HashMap;
    use std::sync::Arc;

    // Mock memory storage for testing
    struct MockStorage;
    impl MemoryStorage for MockStorage {
        fn allocate_buffer(&mut self, _size: usize) -> Result<BufferHandle> {
            Ok(BufferHandle::new(0))
        }
        fn free_buffer(&mut self, _handle: BufferHandle) -> Result<()> {
            Ok(())
        }
        fn copy_to_buffer(&mut self, _handle: BufferHandle, _data: &[u8]) -> Result<()> {
            Ok(())
        }
        fn copy_from_buffer(&self, _handle: BufferHandle, _data: &mut [u8]) -> Result<()> {
            Ok(())
        }
        fn buffer_size(&self, _handle: BufferHandle) -> Result<usize> {
            Ok(0)
        }
        fn allocate_pool(&mut self, _size: usize) -> Result<PoolHandle> {
            Ok(PoolHandle::new(0))
        }
        fn free_pool(&mut self, _handle: PoolHandle) -> Result<()> {
            Ok(())
        }
        fn copy_to_pool(&mut self, _handle: PoolHandle, _offset: usize, _data: &[u8]) -> Result<()> {
            Ok(())
        }
        fn copy_from_pool(&self, _handle: PoolHandle, _offset: usize, _data: &mut [u8]) -> Result<()> {
            Ok(())
        }
        fn pool_size(&self, _handle: PoolHandle) -> Result<usize> {
            Ok(0)
        }
    }

    fn create_test_state() -> ExecutionState<MockStorage> {
        use crate::backend::{BlockDim, GridDim};
        let memory = Arc::new(RwLock::new(MockStorage));
        let context = ExecutionContext::new((0, 0, 0), (0, 0, 0), GridDim::new(1, 1, 1), BlockDim::new(1, 1, 1));
        let labels = HashMap::new();
        ExecutionState::new(1, memory, context, labels)
    }

    #[test]
    fn test_cls_get() {
        let mut state = create_test_state();
        state.lane_states[0].lane.current_class = 42;

        execute_cls_get(&mut state, Register::new(0)).unwrap();

        let value = state.lane_states[0].lane.registers.read_u8(Register::new(0)).unwrap();
        assert_eq!(value, 42);
    }

    #[test]
    fn test_mirror() {
        let mut state = create_test_state();
        state.lane_states[0]
            .lane
            .registers
            .write_u8(Register::new(0), 5)
            .unwrap();

        execute_mirror(&mut state, Register::new(1), Register::new(0)).unwrap();

        let result = state.lane_states[0].lane.registers.read_u8(Register::new(1)).unwrap();
        let expected = get_mirror_pair(5);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_phase_get() {
        let mut state = create_test_state();
        state.lane_states[0].lane.phase_counter = 123;

        execute_phase_get(&mut state, Register::new(0)).unwrap();

        let value = state.lane_states[0].lane.registers.read_u32(Register::new(0)).unwrap();
        assert_eq!(value, 123);
    }

    #[test]
    fn test_phase_adv() {
        let mut state = create_test_state();
        state.lane_states[0].lane.phase_counter = 750;

        execute_phase_adv(&mut state, 30).unwrap();

        // 750 + 30 = 780, 780 % 768 = 12
        assert_eq!(state.lane_states[0].lane.phase_counter, 12);
    }

    #[test]
    fn test_unity_test() {
        let mut state = create_test_state();
        // Assume class 0 is in unity set (depends on atlas-core implementation)
        state.lane_states[0].lane.current_class = 0;

        execute_unity_test(&mut state, Predicate::new(0), 0.0).unwrap();

        let result = state.lane_states[0]
            .lane
            .registers
            .read_predicate(Predicate::new(0))
            .unwrap();
        assert_eq!(result, is_unity(0));
    }

    #[test]
    fn test_bound_map() {
        let mut state = create_test_state();
        // Class 1, page 2, byte 3
        state.lane_states[0]
            .lane
            .registers
            .write_u8(Register::new(0), 1)
            .unwrap();
        state.lane_states[0]
            .lane
            .registers
            .write_u8(Register::new(1), 2)
            .unwrap();
        state.lane_states[0]
            .lane
            .registers
            .write_u8(Register::new(2), 3)
            .unwrap();

        execute_bound_map(
            &mut state,
            Register::new(0),
            Register::new(1),
            Register::new(2),
            Register::new(3),
        )
        .unwrap();

        let result = state.lane_states[0].lane.registers.read_u64(Register::new(3)).unwrap();
        // Expected: class_offset + page_byte_offset
        // class_offset = 1 × 12288 = 12288
        // page_byte_offset = 2 × 256 + 3 = 515
        // total = 12288 + 515 = 12803
        assert_eq!(result, 12803);
    }
}
