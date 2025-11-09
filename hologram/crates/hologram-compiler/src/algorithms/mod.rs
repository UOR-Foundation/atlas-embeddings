//! Quantum Algorithms
//!
//! This module implements quantum algorithms and special quantum states
//! including GHZ states, W states, and the Deutsch-Jozsa algorithm.

pub mod deutsch_jozsa;
pub mod ghz;
pub mod w_states;

// Re-export from deutsch_jozsa
pub use deutsch_jozsa::{deutsch_jozsa, OracleType};

// Re-export from ghz
pub use ghz::{check_ghz_correlation, create_ghz_3, create_ghz_4, create_ghz_n};

// Re-export from w_states
pub use w_states::{check_partial_robustness, create_w_3};
