//! # Atlas Core – Stable Atlas API
//!
//! `atlas-core` provides the public-facing, documentation-driven facade for the Atlas of Resonance
//! Classes. It re-exports the authoritative mathematical engine from [`atlas-embeddings`] and layers
//! a stable Rust and C ABI surface on top for downstream consumers.
//!
//! Detailed behavioural contracts live in `docs/atlas_core_interface.md`.
//!
//! ## Architecture Overview
//!
//! - `atlas-embeddings` owns all mathematical constructs (Atlas graph, labels, exceptional groups).
//! - `atlas-core` offers ergonomic wrappers (`ResonanceClass`, `PhiCoordinate`) and exposes
//!   `#[no_mangle]` functions for the Atlas ISA runtime.
//! - Higher layers (`atlas-isa`, hologram builder, host SDKs) depend on the stable API instead of the
//!   evolving research implementation.
//!
//! ## Quick Start
//!
//! ```
//! use atlas_core::{atlas, Atlas, AtlasLabel, ResonanceClass, phi_encode, get_mirror_pair};
//!
//! // Access the canonical Atlas graph
//! let atlas: &Atlas = atlas();
//! assert_eq!(atlas.num_vertices(), 96);
//!
//! // Classify a byte into a resonance class and inspect its label
//! let class = ResonanceClass::classify(42);
//! let label: AtlasLabel = class.label();
//! assert!(label.is_valid());
//!
//! // Mirror pairing is delegated to atlas-embeddings data
//! let mirror = class.mirror();
//! assert!(atlas.is_mirror_pair(class.id() as usize, mirror.id() as usize));
//!
//! // Φ encoding helpers remain available for address calculations
//! let encoded = phi_encode(7, 128);
//! assert_eq!(encoded, 0x0080_0007);
//! let mirror_id = get_mirror_pair(class.id());
//! assert_ne!(mirror_id, u8::MAX);
//! ```

pub mod abi;
pub mod constants;
pub mod invariants;
pub mod serialize;
pub mod uor;

use std::sync::OnceLock;

pub use atlas_embeddings::foundations::resonance::{
    extend_to_8d as extend_label_to_e8, generate_all_labels, AtlasLabel,
};
pub use atlas_embeddings::Atlas;

pub use constants::*;
pub use invariants::*;
pub use serialize::*;
pub use tracing::*;
pub use uor::*;

use num_rational::Ratio;

/// Access the canonical Atlas graph instance.
///
/// The graph is constructed on first use and shared for the lifetime of the program.
pub fn atlas() -> &'static Atlas {
    static ATLAS: OnceLock<Atlas> = OnceLock::new();
    ATLAS.get_or_init(Atlas::new)
}

/// Result type for Atlas Core operations
pub type Result<T> = std::result::Result<T, AtlasError>;

/// Errors that can occur in Atlas Core operations
#[derive(Debug, thiserror::Error)]
pub enum AtlasError {
    #[error("Invalid class ID: {0} (must be in [0, 96))")]
    InvalidClassId(u32),

    #[error("Invalid page: {0} (must be in [0, 48))")]
    InvalidPage(u32),

    #[error("Invalid byte: {0} (must be in [0, 256))")]
    InvalidByte(u32),

    #[error("Invalid phase: {0} (must be in [0, 768))")]
    InvalidPhase(u32),

    #[error("Unity neutrality violated: delta_sum = {0}")]
    UnityNeutralityViolated(Ratio<i64>),

    #[error("Invalid ratio denominator: {0}")]
    InvalidDenominator(i64),

    #[error("Class mask conflict: kernel requires classes that are unavailable")]
    ClassMaskConflict,

    #[error("Phase window incompatible: phase {current} not in [{begin}, {end})")]
    PhaseWindowIncompatible { current: u32, begin: u32, end: u32 },

    #[error("Boundary out of range: ({page}, {byte})")]
    BoundaryOutOfRange { page: u32, byte: u32 },
}
