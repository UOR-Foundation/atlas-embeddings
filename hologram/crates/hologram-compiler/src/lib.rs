//! # Sigmatics - Unified 768-Cycle Quantum Computing & Circuit Compiler
//!
//! A unified framework combining:
//! - **768-Cycle Quantum Computing**: Deterministic quantum computing in 768-dimensional cycle space
//! - **Constraint-Based Execution**: O(1) multi-qubit operations via linear constraints
//! - **Circuit Compiler**: Pattern-based canonicalization with automatic optimization
//! - **ISA Translation**: Direct compilation to hologram-backends execution
//!
//! ## Overview
//!
//! Sigmatics provides:
//! - **768-Cycle Model**: 768 = 3 × 256 = 96 × 8 (unified geometric representation)
//! - **Quantum Gates**: Single-qubit, two-qubit, and multi-qubit operations
//! - **Constraint Engine**: Linear constraints Σ c_i · p_i ≡ k (mod 768) for complex operations
//! - **Circuit Compiler**: SigmaticsCompiler with canonicalization
//! - **Pattern-Based Optimization**: H²=I, X²=I, Z²=I, HXH=Z, S²=Z, I·I=I
//! - **7 Generators**: mark, copy, swap, merge, split, quote, evaluate
//! - **96-Class System**: Canonical forms with efficient addressing
//! - **Range Operations**: Multi-class vectors for large data
//! - **Transform Algebra**: Rotate (R), Twist (T), and Mirror (M) operations
//!
//! ## Example: Quantum Computing
//!
//! ```text
//! use hologram_compiler::core::QuantumState;
//! use hologram_compiler::gates::{hadamard, pauli_x};
//!
//! // Create quantum state in 768-cycle space
//! let mut state = QuantumState::zero();
//! hadamard(&mut state);
//! pauli_x(&mut state);
//! ```
//!
//! ## Example: Circuit Compilation
//!
//! ```text
//! use hologram_compiler::{SigmaticsCompiler, Canonicalizer};
//!
//! // Compile circuit with canonicalization
//! let circuit = "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21";  // H²
//! let compiled = SigmaticsCompiler::compile(circuit)?;
//!
//! println!("Original: {} ops", compiled.original_ops);   // 4
//! println!("Canonical: {} ops", compiled.canonical_ops); // 1
//! println!("Reduction: {:.1}%", compiled.reduction_pct); // 75.0%
//!
//! // Or just canonicalize
//! let result = Canonicalizer::parse_and_canonicalize(circuit)?;
//! println!("Rewrites: {}", result.rewrite_count);  // 1
//! ```
//!
//! ## Example: Constraint-Based GEMM
//!
//! ```text
//! use hologram_compiler::constraints::{MultiQubitConstraint, NQubitState};
//!
//! // Express GEMM as constraint network
//! // Loop indices → 768-cycle positions
//! // Nested dependencies → linear constraints
//! // O(1) per-iteration complexity
//! let constraint = MultiQubitConstraint::new(vec![1, 1, -1], 0);
//! let state = NQubitState::new(3)?;
//! assert!(constraint.satisfies(&[i, j, k]));
//! ```

// 768-Cycle Quantum Computing Modules (from quantum-768)
pub mod algorithms;
pub mod constraints;
pub mod core;
pub mod gates;

// Sigmatics Circuit Compiler Modules
pub mod ast;
pub mod automorphism_group;
pub mod automorphism_search;
pub mod canonical_repr;
pub mod canonicalization;
pub mod circuit;
pub mod class_system;
pub mod compiler;
pub mod generators;
pub mod lexer;
pub mod multi_class;
pub mod parser;
pub mod pattern;
pub mod rewrite;
pub mod rules;
pub mod types;

/// Build-time generated configuration
///
/// This module contains precomputed tables and optimal automorphism views
/// generated at compile time by the build.rs script.
#[allow(dead_code)]
pub mod build_config {
    include!(concat!(env!("OUT_DIR"), "/build_time_config.rs"));
}

// Re-export all public items from submodules
pub use ast::*;
pub use automorphism_group::*;
pub use automorphism_search::*;
pub use canonical_repr::*;
pub use canonicalization::*;
pub use circuit::*;
pub use class_system::*;
pub use compiler::*;
pub use generators::*;
pub use lexer::*;
pub use multi_class::*;
pub use parser::*;
pub use pattern::*;
pub use rewrite::*;
pub use rules::*;
pub use types::*;

// Re-export quantum-768 core functionality
pub use core::state::Modality;
pub use core::{measure_detailed, measure_quantum_state, project_to_class, verify_determinism, QuantumState};
pub use gates::single_qubit::{apply_gate_sequence, QuantumGate};
pub use gates::{
    apply_hadamard, apply_identity, apply_pauli_x, apply_pauli_y, apply_pauli_z, apply_s_gate, apply_t_gate,
};

// Re-export quantum-768 multi-qubit functionality (always enabled)

pub use core::{validate_born_rule_single_qubit, BornRuleValidation, SuperpositionState};

pub use gates::two_qubit::{
    bell_states::{
        check_bell_correlation, create_bell_phi_minus, create_bell_phi_plus, create_bell_psi_minus,
        create_bell_psi_plus, is_computational_one_from_position, measure_two_qubit_state, BellState,
    },
    gates::{
        apply_cnot, apply_cz, apply_gate_sequence_two_qubit, apply_hadamard_to_qubit, apply_pauli_x_to_qubit,
        apply_pauli_z_to_qubit, apply_single_qubit_gate_to_qubit, apply_swap, GateApplication, TwoQubitGate,
        CNOT_ADVANCEMENT, COMPUTATIONAL_ONE_THRESHOLD, SWAP_ADVANCEMENT,
    },
    state::{CorrelationConstraint, TwoQubitState},
};

// Re-export quantum-768 n-qubit functionality (always enabled)

pub use constraints::{
    measure_qubit, measure_qubits, ConstraintGraph, EntanglementStructure, MultiQubitConstraint, NQubitState,
};

pub use gates::n_qubit::{apply_fredkin, apply_toffoli, TOFFOLI_ADVANCEMENT};

pub use algorithms::{
    check_ghz_correlation, check_partial_robustness, create_ghz_3, create_ghz_4, create_ghz_n, create_w_3,
    deutsch_jozsa, OracleType,
};

#[cfg(test)]
mod build_config_tests {
    use super::build_config::*;

    #[test]
    fn test_canonical_byte_table_size() {
        assert_eq!(CANONICAL_BYTE_TABLE.len(), 96);
    }

    #[test]
    fn test_canonical_bytes_have_b0_zero() {
        // All canonical bytes should have LSB = 0
        for (idx, &byte) in CANONICAL_BYTE_TABLE.iter().enumerate() {
            assert_eq!(
                byte & 1,
                0,
                "Canonical byte for class {} should have b0=0, got 0x{:02X}",
                idx,
                byte
            );
        }
    }

    #[test]
    #[allow(clippy::assertions_on_constants)]
    fn test_optimal_view_h_squared() {
        assert_eq!(OPTIMAL_VIEW_H_SQUARED.dihedral_idx, 0);
        assert_eq!(OPTIMAL_VIEW_H_SQUARED.twist_idx, 0);
        assert_eq!(OPTIMAL_VIEW_H_SQUARED.scope_idx, 0);
        assert!(OPTIMAL_VIEW_H_SQUARED.reduction_ratio < 1.0);
    }

    #[test]
    fn test_reduction_stats_available() {
        assert!(!REDUCTION_STATS.is_empty());

        // Verify at least one reduction stat exists
        let h_squared = REDUCTION_STATS
            .iter()
            .find(|s| s.pattern_name == "H²=I")
            .expect("Should have H²=I reduction stat");

        assert_eq!(h_squared.original_ops, 4);
        assert_eq!(h_squared.canonical_ops, 1);
        assert_eq!(h_squared.reduction_percent, 75.0);
    }
}
