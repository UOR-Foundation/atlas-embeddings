//! Quantum State Representation in 768-Cycle Space
//!
//! This module implements the core `QuantumState` struct that represents a quantum
//! state as a position in the deterministic 768-cycle.
//!
//! ## 768-Cycle Structure
//!
//! ```text
//! State Index = modality × 256 + byte
//!
//! Where:
//!   byte ∈ {0x00..0xFF}     (256 values)
//!   modality ∈ {0,1,2}      (3 modalities)
//!     0 → Neutral (•)
//!     1 → Produce (▲)
//!     2 → Consume (▼)
//! ```
//!
//! ## Examples
//!
//! - (byte=0x00, modality=Neutral) → position 0
//! - (byte=0xFF, modality=Neutral) → position 255
//! - (byte=0x00, modality=Produce) → position 256
//! - (byte=0xFF, modality=Consume) → position 767

use hologram_tracing::perf_span;

/// Total number of states in the 768-cycle
pub const CYCLE_SIZE: u16 = 768;

/// Number of bytes (0x00..0xFF)
pub const BYTE_SPACE: u16 = 256;

/// Number of modalities (Neutral, Produce, Consume)
pub const MODALITY_COUNT: u8 = 3;

/// Modality represents the tri-modal context in the 768-cycle
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Modality {
    /// Neutral state (•) - modality 0
    Neutral = 0,
    /// Produce state (▲) - modality 1
    Produce = 1,
    /// Consume state (▼) - modality 2
    Consume = 2,
}

impl Modality {
    /// Create modality from index (0, 1, or 2)
    pub fn from_index(index: u8) -> Result<Self, String> {
        match index {
            0 => Ok(Modality::Neutral),
            1 => Ok(Modality::Produce),
            2 => Ok(Modality::Consume),
            _ => Err(format!("Invalid modality index: {}. Must be 0, 1, or 2", index)),
        }
    }

    /// Get the numeric index of this modality
    pub fn index(&self) -> u8 {
        *self as u8
    }
}

/// QuantumState represents a quantum state as a position in the 768-cycle
///
/// # Structure
///
/// A quantum state is uniquely identified by its position in [0, 768):
/// - Position = modality × 256 + byte
/// - Position determines measurement outcome deterministically
/// - Evolution = position advancement (mod 768)
///
/// # Example
///
/// ```
/// use hologram_compiler::{QuantumState, Modality};
///
/// // Create |0⟩ state at position 0
/// let state = QuantumState::new(0);
/// assert_eq!(state.position(), 0);
/// assert_eq!(state.byte(), 0x00);
/// assert_eq!(state.modality(), Modality::Neutral);
///
/// // Advance by half-cycle (X gate)
/// let new_state = state.advance(384);
/// assert_eq!(new_state.position(), 384);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct QuantumState {
    /// Position in the 768-cycle [0, 768)
    position: u16,
}

impl QuantumState {
    /// Create a new quantum state at the specified position
    ///
    /// # Arguments
    ///
    /// * `position` - Position in 768-cycle [0, 768)
    ///
    /// # Panics
    ///
    /// Panics if position >= 768
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::QuantumState;
    ///
    /// let state = QuantumState::new(192); // Quarter cycle
    /// assert_eq!(state.position(), 192);
    /// ```
    pub fn new(position: u16) -> Self {
        assert!(position < CYCLE_SIZE, "Position {} must be < {}", position, CYCLE_SIZE);
        Self { position }
    }

    /// Create a new quantum state from byte and modality
    ///
    /// # Arguments
    ///
    /// * `byte` - Byte value [0x00..0xFF]
    /// * `modality` - Tri-modal context
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::{QuantumState, Modality};
    ///
    /// let state = QuantumState::from_byte_modality(0x2A, Modality::Produce);
    /// assert_eq!(state.byte(), 0x2A);
    /// assert_eq!(state.modality(), Modality::Produce);
    /// assert_eq!(state.position(), 256 + 0x2A); // 298
    /// ```
    pub fn from_byte_modality(byte: u8, modality: Modality) -> Self {
        let position = (modality.index() as u16) * BYTE_SPACE + (byte as u16);
        Self::new(position)
    }

    /// Get the current position in the 768-cycle
    pub fn position(&self) -> u16 {
        self.position
    }

    /// Get the byte value [0x00..0xFF] at this position
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::QuantumState;
    ///
    /// let state = QuantumState::new(300);
    /// assert_eq!(state.byte(), 44); // 300 % 256 = 44
    /// ```
    pub fn byte(&self) -> u8 {
        (self.position % BYTE_SPACE) as u8
    }

    /// Get the modality at this position
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::{QuantumState, Modality};
    ///
    /// let state = QuantumState::new(512); // 512 = 2 × 256
    /// assert_eq!(state.modality(), Modality::Consume);
    /// ```
    pub fn modality(&self) -> Modality {
        let modality_index = (self.position / BYTE_SPACE) as u8;
        Modality::from_index(modality_index).expect("Position guarantees valid modality")
    }

    /// Advance the state by a given amount (mod 768)
    ///
    /// This is the core operation for quantum gate application.
    /// Each gate corresponds to a specific advancement amount.
    ///
    /// # Arguments
    ///
    /// * `advancement` - Amount to advance in cycle
    ///
    /// # Returns
    ///
    /// New quantum state at (position + advancement) mod 768
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::QuantumState;
    ///
    /// let state = QuantumState::new(100);
    ///
    /// // Advance by 192 (Hadamard gate)
    /// let new_state = state.advance(192);
    /// assert_eq!(new_state.position(), 292);
    ///
    /// // Advance by 676 (should wrap)
    /// let wrapped = state.advance(676);
    /// assert_eq!(wrapped.position(), (100 + 676) % 768); // 8
    /// ```
    pub fn advance(&self, advancement: u16) -> Self {
        let _span = perf_span!(
            "quantum_state_advance",
            position = self.position,
            advancement = advancement
        );
        let new_position = (self.position + advancement) % CYCLE_SIZE;
        Self::new(new_position)
    }

    /// Advance the state by a signed amount (allowing backward movement)
    ///
    /// # Arguments
    ///
    /// * `advancement` - Signed advancement amount
    ///
    /// # Returns
    ///
    /// New quantum state at (position + advancement) mod 768
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::QuantumState;
    ///
    /// let state = QuantumState::new(100);
    ///
    /// // Advance forward
    /// let forward = state.advance_signed(50);
    /// assert_eq!(forward.position(), 150);
    ///
    /// // Advance backward
    /// let backward = state.advance_signed(-50);
    /// assert_eq!(backward.position(), 50);
    ///
    /// // Wrap backward
    /// let wrapped = state.advance_signed(-150);
    /// assert_eq!(wrapped.position(), (768 + 100 - 150) % 768); // 718
    /// ```
    pub fn advance_signed(&self, advancement: i32) -> Self {
        let _span = perf_span!(
            "quantum_state_advance_signed",
            position = self.position,
            advancement = advancement
        );

        // Handle negative advancements by converting to positive equivalent
        let normalized_advancement = if advancement < 0 {
            let abs_advancement = advancement.unsigned_abs() as u16 % CYCLE_SIZE;
            CYCLE_SIZE - abs_advancement
        } else {
            (advancement as u16) % CYCLE_SIZE
        };

        self.advance(normalized_advancement)
    }

    /// Check if this state is at the origin (position 0)
    pub fn is_origin(&self) -> bool {
        self.position == 0
    }

    /// Distance to another state (shortest path around cycle)
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::QuantumState;
    ///
    /// let state1 = QuantumState::new(100);
    /// let state2 = QuantumState::new(150);
    ///
    /// assert_eq!(state1.distance_to(&state2), 50);
    ///
    /// // Shortest distance wraps around
    /// let state3 = QuantumState::new(700);
    /// let state4 = QuantumState::new(50);
    /// assert_eq!(state3.distance_to(&state4), 118); // 700 -> 768 -> 50 = 118
    /// ```
    pub fn distance_to(&self, other: &Self) -> u16 {
        let forward = if other.position >= self.position {
            other.position - self.position
        } else {
            CYCLE_SIZE - self.position + other.position
        };

        let backward = CYCLE_SIZE - forward;

        forward.min(backward)
    }
}

impl Default for QuantumState {
    /// Default state is |0⟩ at position 0
    fn default() -> Self {
        Self::new(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cycle_constants() {
        assert_eq!(CYCLE_SIZE, 768);
        assert_eq!(BYTE_SPACE, 256);
        assert_eq!(MODALITY_COUNT, 3);
        assert_eq!(CYCLE_SIZE, BYTE_SPACE * (MODALITY_COUNT as u16));
    }

    #[test]
    fn test_modality_creation() {
        assert_eq!(Modality::from_index(0).unwrap(), Modality::Neutral);
        assert_eq!(Modality::from_index(1).unwrap(), Modality::Produce);
        assert_eq!(Modality::from_index(2).unwrap(), Modality::Consume);
        assert!(Modality::from_index(3).is_err());
    }

    #[test]
    fn test_modality_index() {
        assert_eq!(Modality::Neutral.index(), 0);
        assert_eq!(Modality::Produce.index(), 1);
        assert_eq!(Modality::Consume.index(), 2);
    }

    #[test]
    fn test_quantum_state_creation() {
        let state = QuantumState::new(0);
        assert_eq!(state.position(), 0);
        assert_eq!(state.byte(), 0x00);
        assert_eq!(state.modality(), Modality::Neutral);
    }

    #[test]
    fn test_from_byte_modality() {
        // Neutral modality
        let state = QuantumState::from_byte_modality(0x2A, Modality::Neutral);
        assert_eq!(state.position(), 0x2A);
        assert_eq!(state.byte(), 0x2A);
        assert_eq!(state.modality(), Modality::Neutral);

        // Produce modality
        let state = QuantumState::from_byte_modality(0x2A, Modality::Produce);
        assert_eq!(state.position(), 256 + 0x2A);
        assert_eq!(state.byte(), 0x2A);
        assert_eq!(state.modality(), Modality::Produce);

        // Consume modality
        let state = QuantumState::from_byte_modality(0x2A, Modality::Consume);
        assert_eq!(state.position(), 512 + 0x2A);
        assert_eq!(state.byte(), 0x2A);
        assert_eq!(state.modality(), Modality::Consume);
    }

    #[test]
    fn test_advance() {
        let state = QuantumState::new(100);

        // Simple advancement
        let advanced = state.advance(50);
        assert_eq!(advanced.position(), 150);

        // Wrap around
        let wrapped = state.advance(700);
        assert_eq!(wrapped.position(), (100 + 700) % 768); // 32
    }

    #[test]
    fn test_advance_signed() {
        let state = QuantumState::new(100);

        // Forward
        let forward = state.advance_signed(50);
        assert_eq!(forward.position(), 150);

        // Backward
        let backward = state.advance_signed(-50);
        assert_eq!(backward.position(), 50);

        // Wrap backward
        let wrapped = state.advance_signed(-150);
        assert_eq!(wrapped.position(), 718);
    }

    #[test]
    fn test_periodicity() {
        let state = QuantumState::new(42);

        // Full cycle returns to start
        let cycled = state.advance(768);
        assert_eq!(cycled.position(), 42);

        // Multiple cycles
        let multi_cycled = state.advance(768 * 3);
        assert_eq!(multi_cycled.position(), 42);
    }

    #[test]
    fn test_is_origin() {
        assert!(QuantumState::new(0).is_origin());
        assert!(!QuantumState::new(1).is_origin());
        assert!(!QuantumState::new(767).is_origin());
    }

    #[test]
    fn test_distance() {
        let state1 = QuantumState::new(100);
        let state2 = QuantumState::new(150);
        assert_eq!(state1.distance_to(&state2), 50);

        // Shortest path wraps
        let state3 = QuantumState::new(700);
        let state4 = QuantumState::new(50);
        let distance = state3.distance_to(&state4);
        assert_eq!(distance, 118); // 768 - 700 + 50 = 118
    }

    #[test]
    fn test_default_is_origin() {
        let state = QuantumState::default();
        assert!(state.is_origin());
        assert_eq!(state.position(), 0);
    }

    #[test]
    #[should_panic(expected = "Position 768 must be < 768")]
    fn test_invalid_position() {
        QuantumState::new(768);
    }
}
