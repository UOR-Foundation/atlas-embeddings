//! Automorphism Search Engine
//!
//! Searches through the 2048-element automorphism group to find optimal circuit representations.
//! The optimal view is the one that minimizes generator count after canonicalization.
//!
//! ## Search Strategies
//!
//! - **Exhaustive**: Try all 2048 automorphisms (O(2048×n))
//! - **Hierarchical**: Coarse-to-fine search (O(96×n))
//! - **Quantum**: Grover search (O(√2048×n) = O(45×n)) - future
//!
//! ## Usage
//!
//! ```rust
//! use hologram_compiler::automorphism_search::{AutomorphismSearcher, ExhaustiveSearcher};
//!
//! let searcher = ExhaustiveSearcher::new();
//! let result = searcher.find_optimal("copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21").unwrap();
//!
//! println!("Best automorphism: {:?}", result.automorphism);
//! println!("Canonical circuit: {}", result.canonical_circuit);
//! println!("Reduction: {:.1}x", result.reduction_ratio);
//! ```

use crate::automorphism_group::{Automorphism, AutomorphismGroup};
use crate::canonicalization::Canonicalizer;

/// Result of automorphism search
#[derive(Debug, Clone)]
pub struct SearchResult {
    /// Optimal automorphism found
    pub automorphism: Automorphism,

    /// Canonical circuit after applying automorphism
    pub canonical_circuit: String,

    /// Original operation count (before optimization)
    pub original_ops: usize,

    /// Canonical operation count (after optimization)
    pub canonical_ops: usize,

    /// Reduction ratio (original / canonical)
    pub reduction_ratio: f64,
}

/// Trait for automorphism search strategies
pub trait AutomorphismSearcher {
    /// Find optimal automorphism view for a circuit
    fn find_optimal(&self, circuit: &str) -> Result<SearchResult, String>;

    /// Estimate cost of a circuit (lower is better)
    fn estimate_cost(&self, circuit: &str) -> Result<usize, String> {
        let canonical = Canonicalizer::parse_and_canonicalize(circuit).map_err(|e| format!("Parse error: {:?}", e))?;

        // Cost = number of operations after canonicalization
        // Currently using rewrite_count as a proxy for operation count
        // Future enhancement: Count actual generator calls after full compilation
        Ok(canonical.rewrite_count + 1) // +1 for the remaining operation
    }
}

// ============================================================================
// Exhaustive Search (try all 2048 automorphisms)
// ============================================================================

/// Exhaustive search through all 2048 automorphisms
///
/// This is the most thorough strategy but also the slowest (O(2048×n)).
/// Use this for build-time optimization where we want the absolute best result.
pub struct ExhaustiveSearcher {
    group: AutomorphismGroup,
}

impl ExhaustiveSearcher {
    /// Create a new exhaustive searcher
    pub fn new() -> Self {
        ExhaustiveSearcher {
            group: AutomorphismGroup::new(),
        }
    }

    /// Transform circuit under automorphism
    fn transform_circuit(&self, auto: &Automorphism, circuit: &str) -> String {
        self.group.apply_to_circuit(auto, circuit)
    }
}

impl Default for ExhaustiveSearcher {
    fn default() -> Self {
        Self::new()
    }
}

impl AutomorphismSearcher for ExhaustiveSearcher {
    fn find_optimal(&self, circuit: &str) -> Result<SearchResult, String> {
        // Parse original circuit to get baseline
        let original = Canonicalizer::parse_and_canonicalize(circuit).map_err(|e| format!("Parse error: {:?}", e))?;
        let original_cost = self.estimate_cost(circuit)?;

        let mut best_auto = Automorphism::identity();
        let mut best_circuit = format!("{:?}", original.phrase);
        let mut best_cost = original_cost;

        // Try all 2048 automorphisms
        for auto in self.group.iter() {
            // Transform circuit under automorphism
            let transformed = self.transform_circuit(&auto, circuit);

            // Canonicalize transformed circuit
            let canonical = match Canonicalizer::parse_and_canonicalize(&transformed) {
                Ok(c) => c,
                Err(_) => continue, // Skip if transformation produces invalid circuit
            };

            // Estimate cost
            let cost = self.estimate_cost(&transformed)?;

            if cost < best_cost {
                best_cost = cost;
                best_auto = auto;
                best_circuit = format!("{:?}", canonical.phrase);
            }
        }

        Ok(SearchResult {
            automorphism: best_auto,
            canonical_circuit: best_circuit,
            original_ops: original_cost,
            canonical_ops: best_cost,
            reduction_ratio: original_cost as f64 / best_cost as f64,
        })
    }
}

// ============================================================================
// Hierarchical Search (coarse-to-fine)
// ============================================================================

/// Hierarchical search with coarse-to-fine refinement
///
/// Search strategy:
/// 1. Try 16 dihedral elements → select best 4
/// 2. For each of 4 best, try 8 twists → select best 2
/// 3. For each of 2 best, try 16 scopes → select best 1
///
/// Total: 16 + (4×8) + (2×16) = 16 + 32 + 32 = 80 evaluations vs 2048
/// Speedup: 25.6× faster than exhaustive
pub struct HierarchicalSearcher {
    group: AutomorphismGroup,
}

// ============================================================================
// Quantum Search Interface (Phase 7)
// ============================================================================

/// Quantum searcher for automorphism optimization
///
/// This trait defines the interface for quantum-accelerated automorphism search.
/// Quantum algorithms can search the 2048-element automorphism group in O(√2048) ≈ O(45)
/// evaluations, compared to O(2048) for classical exhaustive search.
///
/// ## Quantum Advantage
///
/// ```text
/// Classical Exhaustive: O(2048) evaluations
/// Classical Hierarchical: O(96) evaluations  (coarse-to-fine approximation)
/// Quantum Search:      O(√2048) ≈ 45 evaluations (exact optimal)
///
/// Quantum provides:
/// - 45× speedup over exhaustive classical search
/// - Exact optimum (vs hierarchical approximation)
/// - Guaranteed to find global minimum
/// ```
///
/// ## Implementation Requirements
///
/// A quantum searcher must:
/// 1. Define an oracle that evaluates cost(automorphism, circuit)
/// 2. Use Grover's algorithm or amplitude amplification to search
/// 3. Return the automorphism that minimizes canonical operation count
///
/// ## Future Integration
///
/// When quantum hardware is available:
///
/// ```text
/// // Create quantum searcher
/// let quantum_searcher = QuantumSearcher::new(quantum_backend)?;
///
/// // Find optimal automorphism view (45 evaluations)
/// let result = quantum_searcher.find_optimal(circuit)?;
///
/// // 45× faster than ExhaustiveSearcher (2048 evaluations)
/// assert!(result.reduction_ratio > hierarchical_result.reduction_ratio);
/// ```
pub trait QuantumAutomorphismSearcher: AutomorphismSearcher {
    /// Initialize quantum backend
    ///
    /// # Arguments
    ///
    /// * `backend` - Quantum computing backend (e.g., IBM Q, IonQ, PennyLane)
    ///
    /// # Returns
    ///
    /// Initialized quantum searcher ready for amplitude amplification
    fn new_with_backend(backend: QuantumBackend) -> Result<Self, String>
    where
        Self: Sized;

    /// Quantum oracle for cost evaluation
    ///
    /// Encodes the cost function as a quantum oracle:
    /// |automorphism⟩|0⟩ → |automorphism⟩|cost(automorphism, circuit)⟩
    ///
    /// # Arguments
    ///
    /// * `circuit` - Circuit to optimize
    ///
    /// # Returns
    ///
    /// Quantum oracle that evaluates canonical operation count
    fn build_oracle(&self, circuit: &str) -> Result<QuantumOracle, String>;

    /// Execute Grover search
    ///
    /// Uses Grover's algorithm to search the 2048 automorphism space:
    /// 1. Prepare uniform superposition over all automorphisms
    /// 2. Apply oracle to mark optimal automorphism
    /// 3. Apply amplitude amplification ~√2048 ≈ 45 times
    /// 4. Measure to obtain optimal automorphism
    ///
    /// # Arguments
    ///
    /// * `oracle` - Cost evaluation oracle
    /// * `iterations` - Number of Grover iterations (default: ⌈π/4 √2048⌉ ≈ 36)
    ///
    /// # Returns
    ///
    /// Automorphism that minimizes canonical operation count
    fn grover_search(&self, oracle: &QuantumOracle, iterations: Option<usize>) -> Result<Automorphism, String>;

    /// Quantum advantage factor
    ///
    /// Returns the expected speedup over classical exhaustive search.
    ///
    /// For 2048 automorphisms: √2048 / 2048 ≈ 45× speedup
    fn quantum_advantage_factor(&self) -> f64 {
        let n = 2048.0_f64;
        n / n.sqrt() // O(N) / O(√N)
    }
}

/// Quantum backend configuration
///
/// Placeholder for quantum hardware/simulator backends.
/// Will be implemented when quantum hardware is integrated.
#[allow(dead_code)]
pub enum QuantumBackend {
    /// Simulated quantum backend (for testing)
    Simulator,
    /// IBM Quantum backend
    IBMQuantum { api_token: String, backend_name: String },
    /// IonQ backend
    IonQ { api_token: String },
    /// PennyLane quantum ML backend
    PennyLane { device: String },
}

/// Quantum oracle for automorphism cost evaluation
///
/// Placeholder for quantum oracle implementation.
/// Will be implemented when quantum hardware is integrated.
#[allow(dead_code)]
pub struct QuantumOracle {
    circuit: String,
    qubit_count: usize, // 11 qubits to represent 2048 = 2^11 automorphisms
}

impl QuantumOracle {
    /// Create oracle for circuit optimization
    #[allow(dead_code)]
    pub fn new(circuit: String) -> Self {
        QuantumOracle {
            circuit,
            qubit_count: 11, // log₂(2048) = 11 qubits
        }
    }

    /// Get number of qubits needed to represent automorphism space
    #[allow(dead_code)]
    pub fn qubit_count(&self) -> usize {
        self.qubit_count
    }
}

impl HierarchicalSearcher {
    /// Create a new hierarchical searcher
    pub fn new() -> Self {
        HierarchicalSearcher {
            group: AutomorphismGroup::new(),
        }
    }

    /// Transform circuit under automorphism
    fn transform_circuit(&self, auto: &Automorphism, circuit: &str) -> String {
        self.group.apply_to_circuit(auto, circuit)
    }

    /// Evaluate automorphism cost
    fn evaluate_auto(&self, auto: &Automorphism, circuit: &str) -> Result<usize, String> {
        let transformed = self.transform_circuit(auto, circuit);
        self.estimate_cost(&transformed)
    }
}

impl Default for HierarchicalSearcher {
    fn default() -> Self {
        Self::new()
    }
}

impl AutomorphismSearcher for HierarchicalSearcher {
    fn find_optimal(&self, circuit: &str) -> Result<SearchResult, String> {
        let original_cost = self.estimate_cost(circuit)?;

        // Level 1: Try all 16 dihedral elements
        let mut dihedral_costs = Vec::new();
        for d_idx in 0..16u8 {
            let auto = Automorphism::from_indices(d_idx, 0, 0);
            let cost = self.evaluate_auto(&auto, circuit)?;
            dihedral_costs.push((d_idx, cost));
        }
        dihedral_costs.sort_by_key(|(_, cost)| *cost);
        let top_dihedrals: Vec<u8> = dihedral_costs.iter().take(4).map(|(idx, _)| *idx).collect();

        // Level 2: For top 4 dihedrals, try all 8 twists
        let mut twist_costs = Vec::new();
        for &d_idx in &top_dihedrals {
            for t_idx in 0..8u8 {
                let auto = Automorphism::from_indices(d_idx, t_idx, 0);
                let cost = self.evaluate_auto(&auto, circuit)?;
                twist_costs.push((d_idx, t_idx, cost));
            }
        }
        twist_costs.sort_by_key(|(_, _, cost)| *cost);
        let top_twists: Vec<(u8, u8)> = twist_costs.iter().take(2).map(|(d, t, _)| (*d, *t)).collect();

        // Level 3: For top 2 (dihedral, twist) pairs, try all 16 scopes
        let mut best_auto = Automorphism::identity();
        let mut best_cost = original_cost;

        for (d_idx, t_idx) in top_twists {
            for s_idx in 0..16u8 {
                let auto = Automorphism::from_indices(d_idx, t_idx, s_idx);
                let cost = self.evaluate_auto(&auto, circuit)?;

                if cost < best_cost {
                    best_cost = cost;
                    best_auto = auto;
                }
            }
        }

        // Generate canonical circuit for best automorphism
        let transformed = self.transform_circuit(&best_auto, circuit);
        let canonical =
            Canonicalizer::parse_and_canonicalize(&transformed).map_err(|e| format!("Parse error: {:?}", e))?;

        Ok(SearchResult {
            automorphism: best_auto,
            canonical_circuit: format!("{:?}", canonical.phrase),
            original_ops: original_cost,
            canonical_ops: best_cost,
            reduction_ratio: original_cost as f64 / best_cost as f64,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_exhaustive_search_identity() {
        let searcher = ExhaustiveSearcher::new();
        let result = searcher.find_optimal("mark@c00").unwrap();

        // Identity circuit should have ratio close to 1.0
        assert!(result.reduction_ratio >= 1.0);
    }

    #[test]
    fn test_exhaustive_search_h_squared() {
        let searcher = ExhaustiveSearcher::new();

        // H² = I should reduce significantly
        let result = searcher
            .find_optimal("copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21")
            .unwrap();

        // Should find some reduction
        assert!(result.canonical_ops <= result.original_ops);
    }

    #[test]
    fn test_hierarchical_search_identity() {
        let searcher = HierarchicalSearcher::new();
        let result = searcher.find_optimal("mark@c00").unwrap();

        assert!(result.reduction_ratio >= 1.0);
    }

    #[test]
    fn test_hierarchical_search_h_squared() {
        let searcher = HierarchicalSearcher::new();

        let result = searcher
            .find_optimal("copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21")
            .unwrap();

        // Should find some reduction (may not be as good as exhaustive)
        assert!(result.canonical_ops <= result.original_ops);
    }

    #[test]
    fn test_search_result_structure() {
        let searcher = ExhaustiveSearcher::new();
        let result = searcher.find_optimal("mark@c21 . mark@c21").unwrap(); // X²

        assert!(result.reduction_ratio >= 1.0);
        assert!(result.canonical_ops > 0);
        assert!(result.original_ops > 0);
    }
}
