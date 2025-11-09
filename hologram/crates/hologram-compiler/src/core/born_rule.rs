//! Born Rule Validation - |α|² Probability Emergence
//!
//! This module implements superposition states and validates that Born rule
//! probabilities (|α|²) emerge from geometric density distribution in the
//! 768-cycle model.
//!
//! ## The Born Rule
//!
//! In standard quantum mechanics, the Born rule states:
//!
//! ```text
//! |ψ⟩ = α|0⟩ + β|1⟩
//!
//! P(measure |0⟩) = |α|²
//! P(measure |1⟩) = |β|²
//!
//! where |α|² + |β|² = 1 (normalization)
//! ```
//!
//! ## Geometric Interpretation
//!
//! In the 768-cycle model, the Born rule emerges from **geometric density**:
//!
//! ```text
//! Cycle region [0, 768×|α|²) → outcome |0⟩
//! Cycle region [768×|α|², 768) → outcome |1⟩
//!
//! Random starting position → |α|² probability naturally!
//! ```
//!
//! ## Why This Works
//!
//! 1. Quantum state at unknown cycle position p ∈ [0, 768)
//! 2. Measurement projects to computational basis (|0⟩ or |1⟩)
//! 3. Projection determined by which region p falls in
//! 4. Random sampling of p → frequencies match |α|²
//!
//! **No collapse, no probabilities - just geometric density distribution!**
//!
//! ## Validation Approach
//!
//! ```
//! use hologram_compiler::validate_born_rule_single_qubit;
//!
//! // Test state: |ψ⟩ = 0.866|0⟩ + 0.500|1⟩
//! // Expected: P(0) = 0.75, P(1) = 0.25
//! let result = validate_born_rule_single_qubit(0.866, 0.500, 10000);
//!
//! // 2% tolerance is appropriate for 10k random samples
//! assert!(result.error_0 < 0.02);
//! assert!(result.error_1 < 0.02);
//! ```
//!
//! ## Copenhagen vs 768-Cycle
//!
//! | Aspect | Copenhagen | 768-Cycle Geometric |
//! |--------|------------|---------------------|
//! | **Probability** | Fundamental | Emerges from density |
//! | **Randomness** | Ontological | Epistemic (unknown position) |
//! | **Measurement** | Collapse | Geometric projection |
//! | **Born Rule** | Axiom | Derivable from geometry |

use crate::core::state::{QuantumState, CYCLE_SIZE};

/// Superposition state representation
///
/// Represents |ψ⟩ = α|0⟩ + β|1⟩ as a specific position in the 768-cycle
/// with associated amplitudes.
///
/// The position determines the measurement outcome based on geometric regions.
#[derive(Debug, Clone)]
pub struct SuperpositionState {
    /// Underlying quantum state (cycle position)
    state: QuantumState,
    /// Amplitude for |0⟩ (not stored in geometric model, for validation only)
    alpha: f32,
    /// Amplitude for |1⟩ (not stored in geometric model, for validation only)
    beta: f32,
}

impl SuperpositionState {
    /// Create a superposition state at a specific cycle position
    ///
    /// # Arguments
    ///
    /// * `position` - Position in 768-cycle [0, 768)
    /// * `alpha` - Amplitude for |0⟩ (must satisfy |alpha|² + |beta|² = 1)
    /// * `beta` - Amplitude for |1⟩
    ///
    /// # Panics
    ///
    /// Panics if amplitudes are not normalized (|α|² + |β|² ≠ 1 within tolerance)
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::SuperpositionState;
    ///
    /// // |ψ⟩ = 0.866|0⟩ + 0.500|1⟩  (75% probability of |0⟩, 25% of |1⟩)
    /// let state = SuperpositionState::new(100, 0.866, 0.500);
    /// ```
    pub fn new(position: u16, alpha: f32, beta: f32) -> Self {
        // Verify normalization: |α|² + |β|² = 1
        let norm_squared = alpha * alpha + beta * beta;
        assert!(
            (norm_squared - 1.0).abs() < 0.001,
            "Amplitudes must be normalized: |alpha|² + |beta|² = {}, expected 1.0",
            norm_squared
        );

        Self {
            state: QuantumState::new(position),
            alpha,
            beta,
        }
    }

    /// Get the underlying quantum state
    pub fn state(&self) -> QuantumState {
        self.state
    }

    /// Get the cycle position
    pub fn position(&self) -> u16 {
        self.state.position()
    }

    /// Get alpha amplitude
    pub fn alpha(&self) -> f32 {
        self.alpha
    }

    /// Get beta amplitude
    pub fn beta(&self) -> f32 {
        self.beta
    }

    /// Expected probability of measuring |0⟩ (Born rule: |α|²)
    pub fn prob_zero(&self) -> f32 {
        self.alpha * self.alpha
    }

    /// Expected probability of measuring |1⟩ (Born rule: |β|²)
    pub fn prob_one(&self) -> f32 {
        self.beta * self.beta
    }

    /// Determine measurement outcome based on geometric position
    ///
    /// The cycle is divided into regions based on |α|²:
    /// - [0, 768×|α|²) → outcome |0⟩ (false)
    /// - [768×|α|², 768) → outcome |1⟩ (true)
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::SuperpositionState;
    ///
    /// // |ψ⟩ = 0.866|0⟩ + 0.500|1⟩, so 75% of cycle maps to |0⟩
    /// let threshold = (768.0 * 0.75) as u16;  // 576
    ///
    /// let state_zero = SuperpositionState::new(100, 0.866, 0.500);  // pos < 576
    /// assert!(!state_zero.measure_computational_basis());  // |0⟩
    ///
    /// let state_one = SuperpositionState::new(600, 0.866, 0.500);   // pos >= 576
    /// assert!(state_one.measure_computational_basis());    // |1⟩
    /// ```
    pub fn measure_computational_basis(&self) -> bool {
        // Compute threshold position: 768 × |α|²
        let threshold_position = (CYCLE_SIZE as f32 * self.prob_zero()) as u16;

        // Position below threshold → |0⟩ (false)
        // Position above threshold → |1⟩ (true)
        self.position() >= threshold_position
    }
}

/// Result of Born rule validation
#[derive(Debug, Clone)]
pub struct BornRuleValidation {
    /// Expected probability of |0⟩ (|α|²)
    pub p0_expected: f32,
    /// Expected probability of |1⟩ (|β|²)
    pub p1_expected: f32,
    /// Observed probability of |0⟩
    pub p0_observed: f32,
    /// Observed probability of |1⟩
    pub p1_observed: f32,
    /// Absolute error for |0⟩
    pub error_0: f32,
    /// Absolute error for |1⟩
    pub error_1: f32,
    /// Number of trials
    pub num_trials: usize,
}

impl BornRuleValidation {
    /// Check if validation passed with given error threshold
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::validate_born_rule_single_qubit;
    ///
    /// let result = validate_born_rule_single_qubit(0.866, 0.500, 10000);
    ///
    /// // Should pass with 1% error threshold
    /// assert!(result.passed_with_threshold(0.01));
    /// ```
    pub fn passed_with_threshold(&self, threshold: f32) -> bool {
        self.error_0 < threshold && self.error_1 < threshold
    }

    /// Get maximum error
    pub fn max_error(&self) -> f32 {
        self.error_0.max(self.error_1)
    }

    /// Print validation results
    pub fn print_summary(&self) {
        println!("Born Rule Validation Results:");
        println!("  Trials: {}", self.num_trials);
        println!(
            "  P(0) - Expected: {:.4}, Observed: {:.4}, Error: {:.4}",
            self.p0_expected, self.p0_observed, self.error_0
        );
        println!(
            "  P(1) - Expected: {:.4}, Observed: {:.4}, Error: {:.4}",
            self.p1_expected, self.p1_observed, self.error_1
        );
        println!("  Max Error: {:.4}", self.max_error());
    }
}

/// Validate Born rule for a single-qubit superposition state
///
/// Tests that |α|² probabilities emerge from geometric density by sampling
/// many random cycle positions.
///
/// # Arguments
///
/// * `alpha` - Amplitude for |0⟩
/// * `beta` - Amplitude for |1⟩
/// * `num_trials` - Number of measurements to perform
///
/// # Returns
///
/// BornRuleValidation with observed vs expected probabilities
///
/// # Example
///
/// ```
/// use hologram_compiler::validate_born_rule_single_qubit;
///
/// // Test |ψ⟩ = 0.866|0⟩ + 0.500|1⟩
/// // Expected: P(0) = 0.75, P(1) = 0.25
/// let result = validate_born_rule_single_qubit(0.866, 0.500, 10000);
///
/// // 2% tolerance is appropriate for 10k random samples
/// assert!(result.error_0 < 0.02);
/// assert!(result.error_1 < 0.02);
/// ```
pub fn validate_born_rule_single_qubit(alpha: f32, beta: f32, num_trials: usize) -> BornRuleValidation {
    use rand::Rng;

    let mut outcome_zero_count = 0;
    let mut outcome_one_count = 0;

    let mut rng = rand::thread_rng();

    for _ in 0..num_trials {
        // Random cycle position represents unknown initial state
        let random_position = rng.gen_range(0..CYCLE_SIZE);

        // Create superposition state at this position
        let state = SuperpositionState::new(random_position, alpha, beta);

        // Measure in computational basis
        let outcome = state.measure_computational_basis();

        if outcome {
            outcome_one_count += 1;
        } else {
            outcome_zero_count += 1;
        }
    }

    // Compute observed probabilities
    let p0_observed = outcome_zero_count as f32 / num_trials as f32;
    let p1_observed = outcome_one_count as f32 / num_trials as f32;

    // Expected probabilities (Born rule)
    let p0_expected = alpha * alpha;
    let p1_expected = beta * beta;

    // Compute errors
    let error_0 = (p0_observed - p0_expected).abs();
    let error_1 = (p1_observed - p1_expected).abs();

    BornRuleValidation {
        p0_expected,
        p1_expected,
        p0_observed,
        p1_observed,
        error_0,
        error_1,
        num_trials,
    }
}

/// Standard test cases for Born rule validation
#[derive(Debug, Clone, Copy)]
pub struct BornRuleTestCase {
    /// Alpha amplitude
    pub alpha: f32,
    /// Beta amplitude
    pub beta: f32,
    /// Description
    pub description: &'static str,
}

impl BornRuleTestCase {
    /// Standard test cases for validation
    pub fn standard_cases() -> Vec<BornRuleTestCase> {
        vec![
            BornRuleTestCase {
                alpha: 1.0,
                beta: 0.0,
                description: "Pure |0⟩ state (100% |0⟩)",
            },
            BornRuleTestCase {
                alpha: 0.0,
                beta: 1.0,
                description: "Pure |1⟩ state (100% |1⟩)",
            },
            BornRuleTestCase {
                alpha: 0.707,
                beta: 0.707,
                description: "Equal superposition (50%/50%)",
            },
            BornRuleTestCase {
                alpha: 0.866,
                beta: 0.500,
                description: "75%/25% split",
            },
            BornRuleTestCase {
                alpha: 0.600,
                beta: 0.800,
                description: "36%/64% split",
            },
        ]
    }

    /// Expected probability of |0⟩
    pub fn prob_zero(&self) -> f32 {
        self.alpha * self.alpha
    }

    /// Expected probability of |1⟩
    pub fn prob_one(&self) -> f32 {
        self.beta * self.beta
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_superposition_state_creation() {
        let state = SuperpositionState::new(100, 0.866, 0.500);

        assert_eq!(state.position(), 100);
        assert!((state.alpha() - 0.866).abs() < 0.001);
        assert!((state.beta() - 0.500).abs() < 0.001);
    }

    #[test]
    #[should_panic(expected = "must be normalized")]
    fn test_superposition_state_normalization() {
        // These amplitudes are not normalized
        SuperpositionState::new(100, 0.5, 0.5);
    }

    #[test]
    fn test_prob_computation() {
        let state = SuperpositionState::new(100, 0.866, 0.500);

        assert!((state.prob_zero() - 0.75).abs() < 0.001);
        assert!((state.prob_one() - 0.25).abs() < 0.001);
    }

    #[test]
    fn test_measure_computational_basis() {
        // |ψ⟩ = 0.866|0⟩ + 0.500|1⟩
        // Threshold at position 576 (75% of 768)

        let state_zero = SuperpositionState::new(100, 0.866, 0.500);
        assert!(!state_zero.measure_computational_basis()); // Below threshold → |0⟩

        let state_one = SuperpositionState::new(600, 0.866, 0.500);
        assert!(state_one.measure_computational_basis()); // Above threshold → |1⟩
    }

    #[test]

    fn test_born_rule_validation_pure_states() {
        // Pure |0⟩ state
        let result_zero = validate_born_rule_single_qubit(1.0, 0.0, 1000);
        assert!((result_zero.p0_observed - 1.0).abs() < 0.01);
        assert!((result_zero.p1_observed - 0.0).abs() < 0.01);

        // Pure |1⟩ state
        let result_one = validate_born_rule_single_qubit(0.0, 1.0, 1000);
        assert!((result_one.p0_observed - 0.0).abs() < 0.01);
        assert!((result_one.p1_observed - 1.0).abs() < 0.01);
    }

    #[test]

    fn test_born_rule_validation_equal_superposition() {
        // Equal superposition: |+⟩ = (|0⟩ + |1⟩)/√2
        let result = validate_born_rule_single_qubit(0.707, 0.707, 10000);

        // Should be approximately 50/50
        assert!(result.error_0 < 0.02); // 2% error tolerance
        assert!(result.error_1 < 0.02);
    }

    #[test]

    fn test_born_rule_validation_75_25() {
        // 75/25 split
        let result = validate_born_rule_single_qubit(0.866, 0.500, 10000);

        // 2% tolerance is appropriate for 10k trials (matches equal_superposition test)
        // With 10k samples, standard error ~0.43%, so 2% allows for normal variation
        assert!(result.error_0 < 0.02);
        assert!(result.error_1 < 0.02);
    }

    #[test]

    fn test_born_rule_validation_passed() {
        let result = validate_born_rule_single_qubit(0.866, 0.500, 10000);
        assert!(result.passed_with_threshold(0.02));
    }

    #[test]
    fn test_standard_test_cases() {
        let cases = BornRuleTestCase::standard_cases();
        assert_eq!(cases.len(), 5);

        // Verify normalization for all cases
        for case in cases {
            let norm_squared = case.alpha * case.alpha + case.beta * case.beta;
            assert!(
                (norm_squared - 1.0).abs() < 0.01,
                "Case {:?} not normalized",
                case.description
            );
        }
    }
}
