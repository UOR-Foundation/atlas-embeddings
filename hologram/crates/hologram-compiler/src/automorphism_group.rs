//! Automorphism Group Aut(Atlas₁₂₂₈₈) = D₈ × T₈ × S₁₆
//!
//! The complete automorphism group of the 96-class geometric lattice with 2,048 elements.
//!
//! ## Group Structure
//!
//! ```text
//! Aut(Atlas₁₂₂₈₈) = D₈ × T₈ × S₁₆
//!
//! Where:
//!   D₈  = Dihedral group (16 elements)
//!         - 8 rotations: R₀, R₁, ..., R₇ (on 8-ring context)
//!         - 8 reflections: MR₀, MR₁, ..., MR₇ (mirror + rotation)
//!
//!   T₈  = Twist group (8 elements)
//!         - Phase rotations: T⁰, T¹, ..., T⁷
//!
//!   S₁₆ = Scope group (16 elements)
//!         - Canonical scope permutations
//!
//! Total: 16 × 8 × 16 = 2,048 automorphisms
//! ```
//!
//! ## Automorphism Actions
//!
//! Each automorphism transforms class indices while preserving geometric structure:
//!
//! - **Dihedral (D₈)**: Rotations and reflections on the 8-ring context (ℓ)
//! - **Twist (T₈)**: Phase transformations
//! - **Scope (S₁₆)**: Quadrant and modality mappings
//!
//! ## Usage
//!
//! ```rust
//! use hologram_compiler::automorphism_group::{Automorphism, AutomorphismGroup};
//!
//! let group = AutomorphismGroup::new();
//!
//! // Get a specific automorphism
//! let auto = group.get(42);
//!
//! // Apply to a class index
//! let transformed_class = group.apply(&auto, 21);
//! ```

use crate::types::SigilComponents;

// ============================================================================
// Dihedral Group D₈ (16 elements)
// ============================================================================

/// Dihedral group element D₈
///
/// The dihedral group D₈ has order 16, consisting of:
/// - 8 rotations: R₀, R₁, ..., R₇ (rotation by k positions on 8-ring)
/// - 8 reflections: MR₀, MR₁, ..., MR₇ (mirror followed by rotation)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DihedralElement {
    /// Rotation amount (0..8) on the 8-ring context
    pub rotation: u8,

    /// Reflection flag (mirror)
    pub reflection: bool,
}

impl DihedralElement {
    /// Create a new dihedral element
    pub const fn new(rotation: u8, reflection: bool) -> Self {
        assert!(rotation < 8, "Rotation must be 0..7");
        DihedralElement { rotation, reflection }
    }

    /// Identity element (no rotation, no reflection)
    pub const fn identity() -> Self {
        DihedralElement {
            rotation: 0,
            reflection: false,
        }
    }

    /// Apply dihedral transformation to context value (ℓ)
    pub const fn apply_to_context(self, l: u8) -> u8 {
        let rotated = (l + self.rotation) % 8;
        if self.reflection {
            (8 - rotated) % 8 // Reflection: l → (8 - l) mod 8
        } else {
            rotated
        }
    }

    /// Compose two dihedral elements
    pub const fn compose(self, other: DihedralElement) -> DihedralElement {
        if self.reflection {
            // If first is reflection, second rotation is reversed
            DihedralElement {
                rotation: (self.rotation + 8 - other.rotation) % 8,
                reflection: !other.reflection,
            }
        } else {
            // Normal composition
            DihedralElement {
                rotation: (self.rotation + other.rotation) % 8,
                reflection: other.reflection,
            }
        }
    }
}

// ============================================================================
// Twist Group T₈ (8 elements)
// ============================================================================

/// Twist group element T₈
///
/// The twist group T₈ has order 8, consisting of phase rotations T⁰, T¹, ..., T⁷.
/// These act as phase shifts in the context ring.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TwistElement {
    /// Phase shift amount (0..8)
    pub shift: u8,
}

impl TwistElement {
    /// Create a new twist element
    pub const fn new(shift: u8) -> Self {
        assert!(shift < 8, "Shift must be 0..7");
        TwistElement { shift }
    }

    /// Identity element (no shift)
    pub const fn identity() -> Self {
        TwistElement { shift: 0 }
    }

    /// Apply twist to context value (ℓ)
    pub const fn apply_to_context(self, l: u8) -> u8 {
        (l + self.shift) % 8
    }

    /// Compose two twist elements
    pub const fn compose(self, other: TwistElement) -> TwistElement {
        TwistElement {
            shift: (self.shift + other.shift) % 8,
        }
    }
}

// ============================================================================
// Scope Group S₁₆ (16 elements)
// ============================================================================

/// Scope group element S₁₆
///
/// The scope group S₁₆ has order 16, consisting of canonical permutations
/// of quadrant and modality pairs.
///
/// ## Structure: S₁₆ ≅ Z₄ × Z₄
///
/// Each element is represented as (a, b) where a, b ∈ {0,1,2,3}:
/// - `a`: Quadrant rotation (h₂ → (h₂ + a) mod 4)
/// - `b`: Modality shift (d → (d + b) mod 3)
///
/// Index mapping: `permutation_index = 4*a + b`
///
/// ## Examples
///
/// - Index 0: (0,0) = identity
/// - Index 1: (0,1) = shift modality by 1 (I→X→Z→I)
/// - Index 4: (1,0) = rotate quadrant by 1
/// - Index 5: (1,1) = rotate quadrant + shift modality
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ScopeElement {
    /// Permutation index (0..15)
    /// Encodes (a, b) as 4*a + b where:
    /// - a ∈ {0,1,2,3}: quadrant rotation amount
    /// - b ∈ {0,1,2,3}: modality shift amount
    pub permutation_index: u8,
}

impl ScopeElement {
    /// Create a new scope element
    pub const fn new(permutation_index: u8) -> Self {
        assert!(permutation_index < 16, "Permutation index must be 0..15");
        ScopeElement { permutation_index }
    }

    /// Create from (quadrant_rotation, modality_shift) pair
    pub const fn from_components(quadrant_rotation: u8, modality_shift: u8) -> Self {
        assert!(quadrant_rotation < 4, "Quadrant rotation must be 0..3");
        assert!(modality_shift < 4, "Modality shift must be 0..3");
        ScopeElement {
            permutation_index: 4 * quadrant_rotation + modality_shift,
        }
    }

    /// Get quadrant rotation component (0..3)
    pub const fn quadrant_rotation(self) -> u8 {
        self.permutation_index / 4
    }

    /// Get modality shift component (0..3)
    pub const fn modality_shift(self) -> u8 {
        self.permutation_index % 4
    }

    /// Identity element (no permutation)
    pub const fn identity() -> Self {
        ScopeElement { permutation_index: 0 }
    }

    /// Apply scope permutation to (h₂, d) pair
    ///
    /// Transformation:
    /// - h₂' = (h₂ + a) mod 4 (rotate quadrants)
    /// - d' = (d + b) mod 3 (shift modality cyclically: I→X→Z→I)
    ///
    /// where (a, b) are extracted from permutation_index = 4*a + b
    pub const fn apply_to_scope(self, h2: u8, d: u8) -> (u8, u8) {
        let a = self.quadrant_rotation();
        let b = self.modality_shift();

        let h2_new = (h2 + a) % 4;
        let d_new = (d + b) % 3;

        (h2_new, d_new)
    }

    /// Compose two scope elements
    ///
    /// Composition in Z₄ × Z₄:
    /// (a₁, b₁) ∘ (a₂, b₂) = ((a₁ + a₂) mod 4, (b₁ + b₂) mod 4)
    ///
    /// Note: The modality shift is mod 4 for group closure, but mod 3 when applied
    pub const fn compose(self, other: ScopeElement) -> ScopeElement {
        let a1 = self.quadrant_rotation();
        let b1 = self.modality_shift();
        let a2 = other.quadrant_rotation();
        let b2 = other.modality_shift();

        let a_new = (a1 + a2) % 4;
        let b_new = (b1 + b2) % 4;

        ScopeElement::from_components(a_new, b_new)
    }

    /// Inverse element
    pub const fn inverse(self) -> ScopeElement {
        let a = self.quadrant_rotation();
        let b = self.modality_shift();

        let a_inv = (4 - a) % 4;
        let b_inv = (4 - b) % 4;

        ScopeElement::from_components(a_inv, b_inv)
    }
}

// ============================================================================
// Complete Automorphism
// ============================================================================

/// A single automorphism from Aut(Atlas₁₂₂₈₈)
///
/// Each automorphism is a triple (d, t, s) where:
/// - d ∈ D₈: dihedral element
/// - t ∈ T₈: twist element
/// - s ∈ S₁₆: scope element
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Automorphism {
    /// Dihedral component (16 choices)
    pub dihedral: DihedralElement,

    /// Twist component (8 choices)
    pub twist: TwistElement,

    /// Scope component (16 choices)
    pub scope: ScopeElement,
}

impl Automorphism {
    /// Create a new automorphism
    pub const fn new(dihedral: DihedralElement, twist: TwistElement, scope: ScopeElement) -> Self {
        Automorphism { dihedral, twist, scope }
    }

    /// Identity automorphism
    pub const fn identity() -> Self {
        Automorphism {
            dihedral: DihedralElement::identity(),
            twist: TwistElement::identity(),
            scope: ScopeElement::identity(),
        }
    }

    /// Create from indices
    pub const fn from_indices(dihedral_idx: u8, twist_idx: u8, scope_idx: u8) -> Self {
        assert!(dihedral_idx < 16, "Dihedral index must be 0..15");
        assert!(twist_idx < 8, "Twist index must be 0..7");
        assert!(scope_idx < 16, "Scope index must be 0..15");

        let rotation = dihedral_idx % 8;
        let reflection = dihedral_idx >= 8;

        Automorphism {
            dihedral: DihedralElement { rotation, reflection },
            twist: TwistElement { shift: twist_idx },
            scope: ScopeElement {
                permutation_index: scope_idx,
            },
        }
    }

    /// Get linear index (0..2047) for this automorphism
    pub const fn to_index(self) -> u16 {
        let d_idx = (self.dihedral.rotation + if self.dihedral.reflection { 8 } else { 0 }) as u16;
        let t_idx = self.twist.shift as u16;
        let s_idx = self.scope.permutation_index as u16;

        d_idx * 128 + t_idx * 16 + s_idx
    }

    /// Create from linear index (0..2047)
    pub const fn from_index(index: u16) -> Self {
        assert!(index < 2048, "Index must be 0..2047");

        let d_idx = (index / 128) as u8;
        let t_idx = ((index % 128) / 16) as u8;
        let s_idx = (index % 16) as u8;

        Self::from_indices(d_idx, t_idx, s_idx)
    }

    /// Apply automorphism to sigil components
    pub fn apply_to_components(self, comp: SigilComponents) -> SigilComponents {
        // 1. Apply dihedral to context (ℓ)
        let l = self.dihedral.apply_to_context(comp.l);

        // 2. Apply twist to context (ℓ)
        let l = self.twist.apply_to_context(l);

        // 3. Apply scope to (h₂, d)
        let (h2, d_val) = self.scope.apply_to_scope(comp.h2, comp.d.as_u8());
        let d = crate::types::Modality::from_u8(d_val).expect("Invalid modality");

        SigilComponents { h2, d, l }
    }

    /// Compose two automorphisms
    pub const fn compose(self, other: Automorphism) -> Automorphism {
        Automorphism {
            dihedral: self.dihedral.compose(other.dihedral),
            twist: self.twist.compose(other.twist),
            scope: self.scope.compose(other.scope),
        }
    }
}

// ============================================================================
// Automorphism Group
// ============================================================================

/// The complete automorphism group Aut(Atlas₁₂₂₈₈)
///
/// Contains all 2,048 automorphisms enumerated explicitly.
pub struct AutomorphismGroup {
    // All 2048 automorphisms will be stored here
    // For now, we generate them on-demand
}

impl AutomorphismGroup {
    /// Create the automorphism group
    pub const fn new() -> Self {
        AutomorphismGroup {}
    }

    /// Get automorphism by linear index (0..2047)
    pub const fn get(&self, index: u16) -> Automorphism {
        Automorphism::from_index(index)
    }

    /// Get total number of automorphisms
    pub const fn size(&self) -> usize {
        2048
    }

    /// Apply automorphism to class index
    pub fn apply(&self, auto: &Automorphism, class_index: u8) -> u8 {
        assert!(class_index < 96, "Class index must be 0..95");

        // Decode class to components
        let comp = crate::class_system::decode_class_index(class_index);

        // Apply automorphism
        let transformed = auto.apply_to_components(comp);

        // Encode back to class index
        crate::class_system::components_to_class_index(&transformed)
    }

    /// Apply automorphism to a circuit expression
    ///
    /// Parses the circuit, transforms all class indices, and regenerates the expression.
    pub fn apply_to_circuit(&self, auto: &Automorphism, circuit: &str) -> String {
        use crate::parse;

        // Parse circuit to AST
        let phrase = match parse(circuit) {
            Ok(p) => p,
            Err(_) => return circuit.to_string(), // If parsing fails, return original
        };

        // Transform the phrase
        let transformed = self.transform_phrase(auto, &phrase);

        // Serialize back to string
        format!("{}", transformed)
    }

    /// Transform a phrase by applying automorphism to all class indices
    fn transform_phrase(&self, auto: &Automorphism, phrase: &crate::ast::Phrase) -> crate::ast::Phrase {
        use crate::ast::Phrase;

        match phrase {
            Phrase::Transformed { transform, body } => {
                let transformed_body = self.transform_parallel(auto, body);
                Phrase::Transformed {
                    transform: *transform,
                    body: Box::new(transformed_body),
                }
            }
            Phrase::Parallel(par) => Phrase::Parallel(self.transform_parallel(auto, par)),
        }
    }

    /// Transform a parallel composition
    fn transform_parallel(&self, auto: &Automorphism, par: &crate::ast::Parallel) -> crate::ast::Parallel {
        use crate::ast::Parallel;

        let transformed_branches = par
            .branches
            .iter()
            .map(|seq| self.transform_sequential(auto, seq))
            .collect();

        Parallel::new(transformed_branches)
    }

    /// Transform a sequential composition
    fn transform_sequential(&self, auto: &Automorphism, seq: &crate::ast::Sequential) -> crate::ast::Sequential {
        use crate::ast::Sequential;

        let transformed_items = seq.items.iter().map(|term| self.transform_term(auto, term)).collect();

        Sequential::new(transformed_items)
    }

    /// Transform a term
    fn transform_term(&self, auto: &Automorphism, term: &crate::ast::Term) -> crate::ast::Term {
        use crate::ast::Term;

        match term {
            Term::Operation { generator, target } => {
                let transformed_target = self.transform_target(auto, target);
                Term::Operation {
                    generator: *generator,
                    target: transformed_target,
                }
            }
            Term::Group(par) => Term::Group(Box::new(self.transform_parallel(auto, par))),
        }
    }

    /// Transform a class target (single or range)
    fn transform_target(&self, auto: &Automorphism, target: &crate::types::ClassTarget) -> crate::types::ClassTarget {
        use crate::types::ClassTarget;

        match target {
            ClassTarget::Single(sigil) => ClassTarget::Single(self.transform_class_sigil(auto, sigil)),
            ClassTarget::Range(range) => ClassTarget::Range(self.transform_class_range(auto, range)),
            ClassTarget::CopyPair { src, dst } => ClassTarget::CopyPair {
                src: self.transform_class_sigil(auto, src),
                dst: self.transform_class_sigil(auto, dst),
            },
            ClassTarget::SwapPair { a, b } => ClassTarget::SwapPair {
                a: self.transform_class_sigil(auto, a),
                b: self.transform_class_sigil(auto, b),
            },
            ClassTarget::TripleClass {
                primary,
                context,
                secondary,
            } => ClassTarget::TripleClass {
                primary: self.transform_class_sigil(auto, primary),
                context: self.transform_class_sigil(auto, context),
                secondary: self.transform_class_sigil(auto, secondary),
            },
        }
    }

    /// Transform a class sigil by applying automorphism to class_index
    fn transform_class_sigil(&self, auto: &Automorphism, sigil: &crate::types::ClassSigil) -> crate::types::ClassSigil {
        let transformed_index = self.apply(auto, sigil.class_index);

        crate::types::ClassSigil {
            class_index: transformed_index,
            rotate: sigil.rotate,
            twist: sigil.twist,
            mirror: sigil.mirror,
            scope: sigil.scope,
            page: sigil.page,
        }
    }

    /// Transform a class range by applying automorphism to start and end
    fn transform_class_range(&self, auto: &Automorphism, range: &crate::types::ClassRange) -> crate::types::ClassRange {
        let start = self.apply(auto, range.start_class());
        let end = self.apply(auto, range.end_class());

        // Ensure start < end (automorphism might flip the order)
        let (start, end) = if start < end { (start, end) } else { (end, start) };

        crate::types::ClassRange {
            start_class: start,
            end_class: end,
            rotate: range.rotate,
            twist: range.twist,
            mirror: range.mirror,
            scope: range.scope,
        }
    }

    /// Iterate over all automorphisms
    pub fn iter(&self) -> impl Iterator<Item = Automorphism> {
        (0..2048u16).map(Automorphism::from_index)
    }
}

impl Default for AutomorphismGroup {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dihedral_identity() {
        let id = DihedralElement::identity();
        assert_eq!(id.rotation, 0);
        assert!(!id.reflection);

        // Identity leaves context unchanged
        for l in 0..8 {
            assert_eq!(id.apply_to_context(l), l);
        }
    }

    #[test]
    fn test_dihedral_rotation() {
        let r3 = DihedralElement::new(3, false);
        assert_eq!(r3.apply_to_context(0), 3);
        assert_eq!(r3.apply_to_context(5), 0); // (5 + 3) % 8 = 0
        assert_eq!(r3.apply_to_context(7), 2); // (7 + 3) % 8 = 2
    }

    #[test]
    fn test_dihedral_reflection() {
        let m = DihedralElement::new(0, true);
        assert_eq!(m.apply_to_context(0), 0); // (8 - 0) % 8 = 0
        assert_eq!(m.apply_to_context(1), 7); // (8 - 1) % 8 = 7
        assert_eq!(m.apply_to_context(3), 5); // (8 - 3) % 8 = 5
    }

    #[test]
    fn test_twist_identity() {
        let id = TwistElement::identity();
        assert_eq!(id.shift, 0);

        for l in 0..8 {
            assert_eq!(id.apply_to_context(l), l);
        }
    }

    #[test]
    fn test_twist_shift() {
        let t5 = TwistElement::new(5);
        assert_eq!(t5.apply_to_context(0), 5);
        assert_eq!(t5.apply_to_context(4), 1); // (4 + 5) % 8 = 1
    }

    #[test]
    fn test_automorphism_identity() {
        let id = Automorphism::identity();
        assert_eq!(id.to_index(), 0);

        let group = AutomorphismGroup::new();

        // Identity should leave all classes unchanged
        for class in 0..96 {
            assert_eq!(group.apply(&id, class), class);
        }
    }

    #[test]
    fn test_automorphism_indexing() {
        // Test round-trip conversion
        for i in 0..2048u16 {
            let auto = Automorphism::from_index(i);
            assert_eq!(auto.to_index(), i);
        }
    }

    #[test]
    fn test_automorphism_group_size() {
        let group = AutomorphismGroup::new();
        assert_eq!(group.size(), 2048);
        assert_eq!(group.iter().count(), 2048);
    }

    #[test]
    fn test_automorphism_group_get() {
        let group = AutomorphismGroup::new();

        let auto0 = group.get(0);
        assert_eq!(auto0, Automorphism::identity());

        let auto100 = group.get(100);
        assert_eq!(auto100.to_index(), 100);
    }

    #[test]
    fn test_scope_identity() {
        let id = ScopeElement::identity();
        assert_eq!(id.permutation_index, 0);
        assert_eq!(id.quadrant_rotation(), 0);
        assert_eq!(id.modality_shift(), 0);

        // Identity leaves (h₂, d) unchanged
        for h2 in 0..4 {
            for d in 0..3 {
                assert_eq!(id.apply_to_scope(h2, d), (h2, d));
            }
        }
    }

    #[test]
    fn test_scope_from_components() {
        let s = ScopeElement::from_components(2, 3);
        assert_eq!(s.permutation_index, 11); // 4*2 + 3 = 11
        assert_eq!(s.quadrant_rotation(), 2);
        assert_eq!(s.modality_shift(), 3);
    }

    #[test]
    fn test_scope_quadrant_rotation() {
        let s = ScopeElement::from_components(1, 0);

        // Rotate quadrant by 1
        assert_eq!(s.apply_to_scope(0, 0), (1, 0));
        assert_eq!(s.apply_to_scope(1, 0), (2, 0));
        assert_eq!(s.apply_to_scope(2, 0), (3, 0));
        assert_eq!(s.apply_to_scope(3, 0), (0, 0)); // Wraps around
    }

    #[test]
    fn test_scope_modality_shift() {
        let s = ScopeElement::from_components(0, 1);

        // Shift modality by 1: I(0) → X(1) → Z(2) → I(0)
        assert_eq!(s.apply_to_scope(0, 0), (0, 1)); // I → X
        assert_eq!(s.apply_to_scope(0, 1), (0, 2)); // X → Z
        assert_eq!(s.apply_to_scope(0, 2), (0, 0)); // Z → I (mod 3)
    }

    #[test]
    fn test_scope_combined_transformation() {
        let s = ScopeElement::from_components(2, 1);

        // Rotate quadrant by 2, shift modality by 1
        assert_eq!(s.apply_to_scope(1, 0), (3, 1)); // h₂: 1+2=3, d: 0+1=1
        assert_eq!(s.apply_to_scope(3, 2), (1, 0)); // h₂: (3+2)%4=1, d: (2+1)%3=0
    }

    #[test]
    fn test_scope_compose() {
        let s1 = ScopeElement::from_components(1, 2);
        let s2 = ScopeElement::from_components(2, 1);

        let composed = s1.compose(s2);

        // (1,2) ∘ (2,1) = ((1+2)%4, (2+1)%4) = (3, 3)
        assert_eq!(composed.quadrant_rotation(), 3);
        assert_eq!(composed.modality_shift(), 3);
    }

    #[test]
    fn test_scope_inverse() {
        for i in 0..16u8 {
            let s = ScopeElement::new(i);
            let s_inv = s.inverse();
            let composed = s.compose(s_inv);

            // s ∘ s⁻¹ = identity
            assert_eq!(composed, ScopeElement::identity());
        }
    }

    #[test]
    fn test_scope_group_closure() {
        // Verify all compositions stay within S₁₆
        for i in 0..16u8 {
            for j in 0..16u8 {
                let s1 = ScopeElement::new(i);
                let s2 = ScopeElement::new(j);
                let composed = s1.compose(s2);

                // Result must be in range 0..15
                assert!(composed.permutation_index < 16);
            }
        }
    }

    #[test]
    fn test_scope_associativity() {
        let s1 = ScopeElement::from_components(1, 2);
        let s2 = ScopeElement::from_components(2, 3);
        let s3 = ScopeElement::from_components(3, 1);

        // (s1 ∘ s2) ∘ s3 = s1 ∘ (s2 ∘ s3)
        let left = s1.compose(s2).compose(s3);
        let right = s1.compose(s2.compose(s3));

        assert_eq!(left, right);
    }

    #[test]
    fn test_apply_to_circuit_identity() {
        let group = AutomorphismGroup::new();
        let id = Automorphism::identity();

        // Identity automorphism should leave circuit unchanged
        let circuit = "mark @ c21";
        let transformed = group.apply_to_circuit(&id, circuit);

        // Parse both to verify they're equivalent (whitespace may differ)
        let original = crate::parse(circuit).unwrap();
        let result = crate::parse(&transformed).unwrap();

        assert_eq!(format!("{:?}", original), format!("{:?}", result));
    }

    #[test]
    fn test_apply_to_circuit_simple() {
        let group = AutomorphismGroup::new();

        // Create a non-identity automorphism
        let auto = Automorphism::from_indices(1, 0, 0); // Rotation by 1

        let circuit = "mark @ c00";
        let transformed = group.apply_to_circuit(&auto, circuit);

        // The class should be transformed
        assert!(transformed.contains("mark"));
        // Result should be parseable
        assert!(crate::parse(&transformed).is_ok());
    }

    #[test]
    fn test_apply_to_circuit_sequential() {
        let group = AutomorphismGroup::new();
        let auto = Automorphism::from_indices(2, 1, 0);

        let circuit = "mark@c05 . copy@c21->c22";
        let transformed = group.apply_to_circuit(&auto, circuit);

        // Result should be parseable
        let parsed = crate::parse(&transformed);
        assert!(
            parsed.is_ok(),
            "Failed to parse transformed circuit: {}\nError: {:?}",
            transformed,
            parsed.err()
        );

        // Should still have mark and copy
        assert!(transformed.contains("mark"));
        assert!(transformed.contains("copy"));
    }

    #[test]
    fn test_apply_to_circuit_range() {
        let group = AutomorphismGroup::new();
        let auto = Automorphism::from_indices(0, 0, 1); // Scope transformation

        let circuit = "merge@c[0..9]";
        let transformed = group.apply_to_circuit(&auto, circuit);

        // Result should be parseable
        let parsed = crate::parse(&transformed);
        assert!(parsed.is_ok(), "Failed to parse: {}", transformed);

        // Should still be a range merge
        assert!(transformed.contains("merge"));
        assert!(transformed.contains("["));
        assert!(transformed.contains("]"));
    }

    #[test]
    fn test_apply_to_circuit_invalid() {
        let group = AutomorphismGroup::new();
        let auto = Automorphism::from_indices(5, 3, 2);

        // Invalid circuit should be returned unchanged
        let circuit = "invalid syntax here";
        let transformed = group.apply_to_circuit(&auto, circuit);

        assert_eq!(transformed, circuit);
    }

    #[test]
    fn test_transform_preserves_structure() {
        let group = AutomorphismGroup::new();
        let auto = Automorphism::from_indices(3, 2, 1);

        // Complex circuit with grouping and parallel
        let circuit = "(mark@c01 . copy@c02->c03) || mark@c03";
        let transformed = group.apply_to_circuit(&auto, circuit);

        // Result should be parseable
        let parsed = crate::parse(&transformed);
        assert!(parsed.is_ok(), "Failed to parse: {}", transformed);

        // Should preserve structure (grouping and parallel)
        assert!(transformed.contains("("));
        assert!(transformed.contains(")"));
        assert!(transformed.contains("||"));
    }
}
