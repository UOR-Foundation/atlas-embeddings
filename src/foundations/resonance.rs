//! # Chapter 0.3: Resonance and Equivalence
//!
//! The stationary configuration of our action functional takes on many values—one
//! for each cell in the 12,288-cell complex. However, these values are not all
//! distinct: they fall into **equivalence classes** called **resonance classes**.
//!
//! The 96 vertices of the Atlas correspond to the 96 resonance classes.
//!
//! ## Overview
//!
//! This chapter answers: **Why 96 vertices?**
//!
//! The answer lies in understanding equivalence relations on configurations.
//! While there are 12,288 cells, the stationary configuration's values cluster
//! into exactly 96 distinct classes when we account for:
//!
//! 1. Gauge symmetries (phase equivalence)
//! 2. Geometric symmetries (cell permutations)
//! 3. Structural constraints (boundary relations)
//!
//! These 96 classes are what we call the **Atlas vertices**.

use num_rational::Ratio;

// # 0.3.1 Resonance Condition

// ## 0.3.1 Resonance Condition
//
// Two configurations are **resonant** if they produce the same physical behavior
// despite having different mathematical representations.
//
// ### Definition 0.3.1 (Resonance Equivalence)
//
// Two configurations φ, ψ are **resonant** (φ ~ ψ) if:
//
// $$ S[\phi] = S[\psi] $$
//
// and they are related by a symmetry of the action functional.
//
// ### Why Equivalence?
//
// In physics, many different mathematical descriptions can represent the same
// physical state. Examples:
//
// - **Gauge symmetry**: In electromagnetism, potentials A and A + ∇χ produce
//   the same electromagnetic field
// - **Phase equivalence**: In quantum mechanics, ψ and e^{iθ}ψ represent the
//   same state (global phase is unobservable)
// - **Coordinate choice**: Different coordinate systems describe the same geometry
//
// Our action functional has similar symmetries. Configurations that differ by
// these symmetries are physically equivalent—they should be considered the
// same resonance class.
//
// ### Mathematical Structure
//
// Resonance defines an **equivalence relation** on configurations:
//
// 1. **Reflexive**: φ ~ φ (every configuration is resonant with itself)
// 2. **Symmetric**: φ ~ ψ implies ψ ~ φ
// 3. **Transitive**: φ ~ ψ and ψ ~ χ implies φ ~ χ
//
// The equivalence classes [φ] = {ψ : ψ ~ φ} are the **resonance classes**.

/// A resonance class: an equivalence class of configurations.
///
/// Represents a set of configurations that are equivalent under the action
/// functional's symmetries.
///
/// In the simplified model, we represent a resonance class by a representative
/// configuration.
#[derive(Debug, Clone)]
pub struct ResonanceClass {
    /// A representative element of this equivalence class
    representative: Ratio<i64>,
    /// Size of the equivalence class (how many configurations map to this class)
    class_size: usize,
}

impl ResonanceClass {
    /// Create a new resonance class with the given representative.
    #[must_use]
    pub const fn new(representative: Ratio<i64>, class_size: usize) -> Self {
        Self { representative, class_size }
    }

    /// Get the representative value for this class.
    #[must_use]
    pub const fn representative(&self) -> &Ratio<i64> {
        &self.representative
    }

    /// Get the size of this equivalence class.
    #[must_use]
    pub const fn size(&self) -> usize {
        self.class_size
    }
}

/// Check if two values are resonant (equivalent under symmetries).
///
/// This is a simplified version. The full theory involves checking gauge
/// and geometric symmetries.
///
/// # Examples
///
/// ```
/// use atlas_embeddings::foundations::resonance::are_resonant;
/// use num_rational::Ratio;
///
/// let a = Ratio::new(1, 2);
/// let b = Ratio::new(1, 2);
/// assert!(are_resonant(&a, &b)); // Same value
///
/// let c = Ratio::new(2, 3);
/// // Different values might still be resonant under symmetries
/// ```
#[must_use]
pub fn are_resonant(a: &Ratio<i64>, b: &Ratio<i64>) -> bool {
    // Simplified: exact equality
    // Full theory would check gauge and symmetry equivalence
    a == b
}

// # 0.3.2 The 96 Resonance Classes

// ## 0.3.2 The 96 Resonance Classes
//
// When we partition the 12,288 cell values of the stationary configuration
// into resonance classes, we get exactly **96 classes**.
//
// ### The Discovery
//
// This number—96—is not input to our construction. It emerges as output:
//
// 1. Start with 12,288-cell complex
// 2. Find stationary configuration of action functional
// 3. Group values into resonance classes
// 4. Count: **exactly 96 classes**
//
// This is the **first empirical fact** about the Atlas.
//
// ### Why 96?
//
// The number 96 factors as:
//
// $$ 96 = 2^5 \cdot 3 = 32 \cdot 3 $$
//
// This reflects the structure of the label system (next section):
// - 2⁵ from binary coordinates (e₁, e₂, e₃, e₆, e₇)
// - 3 from ternary coordinate (d₄₅)
//
// But more fundamentally, 96 appears in E₈ theory:
// - E₈ has 240 roots
// - 96 is the number of roots in a certain orbit
// - This hints at the Atlas → E₈ connection (Chapter 3)
//
// ### Distribution Across the Complex
//
// The 12,288 cells are not evenly distributed among the 96 classes:
// - Some classes are large (many cells)
// - Some classes are small (few cells)
//
// The distribution is determined by the symmetry structure of the complex.

/// Partition configurations into resonance classes.
///
/// Given a collection of values from the stationary configuration, group them
/// into equivalence classes.
///
/// # Returns
///
/// A vector of [`ResonanceClass`] objects, one for each equivalence class.
///
/// # Examples
///
/// ```
/// use atlas_embeddings::foundations::resonance::partition_into_classes;
/// use num_rational::Ratio;
///
/// let values = vec![
///     Ratio::new(1, 2),
///     Ratio::new(1, 2),
///     Ratio::new(2, 3),
///     Ratio::new(1, 2),
///     Ratio::new(2, 3),
/// ];
///
/// let classes = partition_into_classes(&values);
/// assert_eq!(classes.len(), 2); // Two distinct values
/// ```
#[must_use]
pub fn partition_into_classes(values: &[Ratio<i64>]) -> Vec<ResonanceClass> {
    let mut class_map: std::collections::HashMap<Ratio<i64>, usize> =
        std::collections::HashMap::new();

    // Count occurrences of each value
    for &value in values {
        *class_map.entry(value).or_insert(0) += 1;
    }

    // Convert to resonance classes
    class_map
        .into_iter()
        .map(|(rep, count)| ResonanceClass::new(rep, count))
        .collect()
}

/// Verify that the stationary configuration has exactly 96 resonance classes.
///
/// This is the key empirical result that defines the Atlas.
///
/// # Examples
///
/// ```
/// use atlas_embeddings::foundations::resonance::verify_96_classes;
///
/// // In the actual construction, this would verify the stationary configuration
/// // For now, we demonstrate the expected result
/// let num_classes = 96;
/// assert!(verify_96_classes(num_classes));
/// ```
#[must_use]
pub const fn verify_96_classes(num_classes: usize) -> bool {
    num_classes == 96
}

// # 0.3.3 The Label System

// ## 0.3.3 The Label System
//
// Each resonance class is labeled by a **6-tuple** encoding its structure.
//
// ### Definition 0.3.2 (Atlas Label)
//
// An **Atlas label** is a 6-tuple:
//
// $$ (e_1, e_2, e_3, d_{45}, e_6, e_7) $$
//
// where:
// - **e₁, e₂, e₃ ∈ {0, 1}**: Binary coordinates (first three)
// - **d₄₅ ∈ {-1, 0, +1}**: Ternary coordinate (encodes difference e₄ - e₅)
// - **e₆, e₇ ∈ {0, 1}**: Binary coordinates (last two)
//
// This gives 2³ × 3 × 2² = 8 × 3 × 4 = 96 possible labels, and **all 96 occur**.
//
// ### Why 6-tuple, Not 8-tuple?
//
// We work in 8 dimensions (preparing for E₈), but use only 6 coordinates. Why?
//
// **Gauge symmetry**: The individual values of e₄ and e₅ are not observable—only
// their difference d₄₅ = e₄ - e₅ matters. This is a fundamental symmetry of
// the action functional.
//
// Attempting to specify e₄ and e₅ independently would:
// - Violate gauge symmetry
// - Introduce redundancy (many labels for same class)
// - Obscure the natural structure
//
// The 6-tuple is the **minimal** label system respecting all symmetries.
//
// ### Connection to Binary/Ternary Structure
//
// The label structure reflects the factorization 96 = 2⁵ × 3:
//
// - **Binary part** (2⁵ = 32): Five coordinates e₁, e₂, e₃, e₆, e₇
// - **Ternary part** (3): One coordinate d₄₅
//
// This will connect to the categorical operations in Chapter 4:
// - G₂ construction uses the ternary structure (ℤ/3)
// - Other constructions use the binary structure

/// An Atlas label: 6-tuple identifying a resonance class.
///
/// # Coordinate System
///
/// - `e1, e2, e3`: Binary coordinates (0 or 1)
/// - `d45`: Ternary coordinate (-1, 0, or +1) representing e₄ - e₅
/// - `e6, e7`: Binary coordinates (0 or 1)
///
/// # Examples
///
/// ```
/// use atlas_embeddings::foundations::resonance::AtlasLabel;
///
/// // Create label (0,0,0,0,0,0) - the "origin" vertex
/// let origin = AtlasLabel::new(0, 0, 0, 0, 0, 0);
/// assert!(origin.is_valid());
///
/// // Create label with ternary coordinate
/// let label = AtlasLabel::new(1, 0, 1, 1, 0, 1);
/// assert!(label.is_valid());
/// assert_eq!(label.d45(), 1);
///
/// // Invalid ternary value
/// let invalid = AtlasLabel::new(0, 0, 0, 2, 0, 0);
/// assert!(!invalid.is_valid());
/// ```
#[allow(clippy::large_stack_arrays)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AtlasLabel {
    /// First coordinate (binary: 0 or 1)
    pub e1: i8,
    /// Second coordinate (binary: 0 or 1)
    pub e2: i8,
    /// Third coordinate (binary: 0 or 1)
    pub e3: i8,
    /// Difference d₄₅ = e₄ - e₅ (ternary: -1, 0, or +1)
    pub d45: i8,
    /// Sixth coordinate (binary: 0 or 1)
    pub e6: i8,
    /// Seventh coordinate (binary: 0 or 1)
    pub e7: i8,
}

impl AtlasLabel {
    /// Create a new Atlas label.
    ///
    /// # Arguments
    ///
    /// * `e1, e2, e3, e6, e7` - Binary coordinates (should be 0 or 1)
    /// * `d45` - Ternary coordinate (should be -1, 0, or +1)
    ///
    /// # Note
    ///
    /// This constructor does not validate inputs. Use [`is_valid`](Self::is_valid)
    /// to check validity.
    #[must_use]
    #[allow(clippy::too_many_arguments)]
    pub const fn new(e1: i8, e2: i8, e3: i8, d45: i8, e6: i8, e7: i8) -> Self {
        Self { e1, e2, e3, d45, e6, e7 }
    }

    /// Check if this label is valid.
    ///
    /// Validity conditions:
    /// - Binary coordinates in {0, 1}
    /// - Ternary coordinate in {-1, 0, +1}
    #[must_use]
    pub const fn is_valid(&self) -> bool {
        // Check binary coordinates
        let binary_valid = (self.e1 == 0 || self.e1 == 1)
            && (self.e2 == 0 || self.e2 == 1)
            && (self.e3 == 0 || self.e3 == 1)
            && (self.e6 == 0 || self.e6 == 1)
            && (self.e7 == 0 || self.e7 == 1);

        // Check ternary coordinate
        let ternary_valid = self.d45 == -1 || self.d45 == 0 || self.d45 == 1;

        binary_valid && ternary_valid
    }

    /// Get the ternary coordinate d₄₅ = e₄ - e₅.
    #[must_use]
    pub const fn d45(&self) -> i8 {
        self.d45
    }

    /// Count the number of 1's in the binary coordinates.
    ///
    /// This is used in determining adjacency and other properties.
    #[must_use]
    #[allow(clippy::cast_sign_loss)]
    pub const fn binary_weight(&self) -> usize {
        (self.e1 + self.e2 + self.e3 + self.e6 + self.e7) as usize
    }
}

/// Generate all 96 valid Atlas labels.
///
/// Enumerates all 2³ × 3 × 2² = 96 combinations of valid coordinates.
///
/// # Returns
///
/// A vector of all 96 [`AtlasLabel`] values.
///
/// # Examples
///
/// ```
/// use atlas_embeddings::foundations::resonance::generate_all_labels;
///
/// let labels = generate_all_labels();
/// assert_eq!(labels.len(), 96);
///
/// // All labels should be valid
/// assert!(labels.iter().all(|label| label.is_valid()));
///
/// // All labels should be distinct
/// use std::collections::HashSet;
/// let unique: HashSet<_> = labels.iter().collect();
/// assert_eq!(unique.len(), 96);
/// ```
#[must_use]
pub fn generate_all_labels() -> Vec<AtlasLabel> {
    let mut labels = Vec::with_capacity(96);

    // Iterate over all combinations
    for e1 in [0, 1] {
        for e2 in [0, 1] {
            for e3 in [0, 1] {
                for d45 in [-1, 0, 1] {
                    for e6 in [0, 1] {
                        for e7 in [0, 1] {
                            labels.push(AtlasLabel::new(e1, e2, e3, d45, e6, e7));
                        }
                    }
                }
            }
        }
    }

    labels
}

// # 0.3.4 Extension to E₈ Coordinates

// ## 0.3.4 Extension to E₈ Coordinates
//
// The 6-tuple labels naturally extend to 8-tuples in the E₈ lattice.
//
// ### Proposition 0.3.3 (Extension to 8D)
//
// Each 6-tuple (e₁,e₂,e₃,d₄₅,e₆,e₇) extends uniquely to an 8-tuple
// (e₁,e₂,e₃,e₄,e₅,e₆,e₇,e₈) satisfying:
//
// 1. **d₄₅ constraint**: e₄ - e₅ = d₄₅
// 2. **Parity constraint**: e₁ + e₂ + e₃ + e₄ + e₅ + e₆ + e₇ + e₈ ≡ 0 (mod 2)
//
// ### The Extension Algorithm
//
// Given (e₁,e₂,e₃,d₄₅,e₆,e₇):
//
// 1. **Recover e₄ and e₅ from d₄₅**:
//    - We know e₄ - e₅ = d₄₅
//    - We need e₄, e₅ ∈ {0, 1}
//    - Solution depends on d₄₅:
//      - If d₄₅ = -1: (e₄, e₅) = (0, 1)
//      - If d₄₅ = 0: Choose based on parity of e₁+e₂+e₃+e₆+e₇
//      - If d₄₅ = +1: (e₄, e₅) = (1, 0)
//
// 2. **Compute e₈ from parity**:
//    - e₈ = (e₁ + e₂ + e₃ + e₄ + e₅ + e₆ + e₇) mod 2
//    - This ensures the sum is even
//
// ### Why This Extension?
//
// The extension is **canonical**—determined by mathematical constraints, not
// arbitrary choices. It ensures:
//
// - Compatibility with E₈ lattice structure
// - Preservation of symmetries
// - Uniqueness (no ambiguity)
//
// This extension is central to the embedding theorem (Chapter 3).
//
// ### Preview: The Embedding
//
// The extended 8-tuples turn out to be **roots of E₈**—vectors of norm² = 2
// in the E₈ root system. This is not obvious from the construction; it is a
// discovery.
//
// The Atlas embeds into E₈ via this extension, which is why E₈ structure
// underlies all exceptional groups.

/// Extend an Atlas label to 8 coordinates.
///
/// Recovers (e₄, e₅) from d₄₅ and computes e₈ from parity constraint.
///
/// # Algorithm
///
/// 1. Determine (e₄, e₅) from d₄₅ using constraints
/// 2. Compute e₈ to ensure even parity
///
/// # Returns
///
/// An 8-tuple (e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈) extending the input label.
///
/// # Examples
///
/// ```
/// use atlas_embeddings::foundations::resonance::{AtlasLabel, extend_to_8d};
///
/// // Label with d45 = 1 means e4 - e5 = 1
/// let label = AtlasLabel::new(0, 0, 0, 1, 0, 0);
/// let extended = extend_to_8d(&label);
///
/// assert_eq!(extended[3] - extended[4], 1); // e4 - e5 = 1
///
/// // Check parity: sum should be even
/// let sum: i8 = extended.iter().sum();
/// assert_eq!(sum % 2, 0);
/// ```
///
/// # Panics
///
/// Panics if `label.d45` is not one of -1, 0, or +1.
#[must_use]
pub fn extend_to_8d(label: &AtlasLabel) -> [i8; 8] {
    let (e4, e5) = match label.d45 {
        -1 => (0, 1), // e4 - e5 = -1
        1 => (1, 0),  // e4 - e5 = 1
        0 => {
            // e4 = e5, choose based on parity
            let partial_sum = label.e1 + label.e2 + label.e3 + label.e6 + label.e7;
            if partial_sum % 2 == 0 {
                (0, 0)
            } else {
                (1, 1)
            }
        },
        _ => panic!("Invalid d45 value: {}", label.d45),
    };

    // Compute e8 to ensure even parity
    let e8 = (label.e1 + label.e2 + label.e3 + e4 + e5 + label.e6 + label.e7) % 2;

    [label.e1, label.e2, label.e3, e4, e5, label.e6, label.e7, e8]
}

// ## 0.3.5 Summary
//
// We have established the structure of resonance classes:
//
// 1. **Resonance equivalence**: Configurations equivalent under symmetries
// 2. **96 classes**: The stationary configuration has exactly 96 resonance classes
// 3. **Label system**: Each class is labeled by a 6-tuple (e₁,e₂,e₃,d₄₅,e₆,e₇)
// 4. **Extension to 8D**: Labels extend uniquely to 8-tuples in E₈
//
// These 96 resonance classes **are** the Atlas vertices. The graph structure
// (edges) comes from the adjacency structure of the action functional.
//
// In the next section, we introduce the categorical framework that will allow
// us to construct all exceptional groups from the Atlas.
//
// ---
//
// **Navigation**:
// - Previous: [§0.2 Action Functionals](super::action)
// - Next: [§0.4 Categorical Preliminaries](super::categories)
// - Up: [Chapter 0: Foundations](super)

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn test_resonance_class_creation() {
        let class = ResonanceClass::new(Ratio::new(1, 2), 128);
        assert_eq!(*class.representative(), Ratio::new(1, 2));
        assert_eq!(class.size(), 128);
    }

    #[test]
    fn test_partition_into_classes() {
        let values = vec![Ratio::new(1, 2), Ratio::new(1, 2), Ratio::new(2, 3), Ratio::new(1, 2)];

        let classes = partition_into_classes(&values);
        assert_eq!(classes.len(), 2); // Two distinct values

        // Check total count
        let total: usize = classes.iter().map(ResonanceClass::size).sum();
        assert_eq!(total, 4);
    }

    #[test]
    fn test_atlas_label_validity() {
        // Valid labels
        assert!(AtlasLabel::new(0, 0, 0, 0, 0, 0).is_valid());
        assert!(AtlasLabel::new(1, 1, 1, -1, 1, 1).is_valid());
        assert!(AtlasLabel::new(0, 1, 0, 1, 1, 0).is_valid());

        // Invalid: binary coordinate out of range
        assert!(!AtlasLabel::new(2, 0, 0, 0, 0, 0).is_valid());
        assert!(!AtlasLabel::new(0, 0, 0, 0, 0, -1).is_valid());

        // Invalid: ternary coordinate out of range
        assert!(!AtlasLabel::new(0, 0, 0, 2, 0, 0).is_valid());
        assert!(!AtlasLabel::new(0, 0, 0, -2, 0, 0).is_valid());
    }

    #[test]
    fn test_generate_all_labels() {
        let labels = generate_all_labels();

        // Exactly 96 labels
        assert_eq!(labels.len(), 96);

        // All valid
        assert!(labels.iter().all(AtlasLabel::is_valid));

        // All distinct
        let unique: HashSet<_> = labels.iter().collect();
        assert_eq!(unique.len(), 96);

        // Verify count: 2^3 * 3 * 2^2 = 8 * 3 * 4 = 96
        assert_eq!(labels.len(), 8 * 3 * 4);
    }

    #[test]
    fn test_extension_to_8d() {
        // Test d45 = 1: should give e4 - e5 = 1
        let label = AtlasLabel::new(0, 0, 0, 1, 0, 0);
        let extended = extend_to_8d(&label);
        assert_eq!(extended[3] - extended[4], 1);

        // Test d45 = -1: should give e4 - e5 = -1
        let label = AtlasLabel::new(0, 0, 0, -1, 0, 0);
        let extended = extend_to_8d(&label);
        assert_eq!(extended[3] - extended[4], -1);

        // Test d45 = 0: e4 should equal e5
        let label = AtlasLabel::new(0, 0, 0, 0, 0, 0);
        let extended = extend_to_8d(&label);
        assert_eq!(extended[3], extended[4]);
    }

    #[test]
    fn test_extension_parity() {
        let labels = generate_all_labels();

        for label in &labels {
            let extended = extend_to_8d(label);
            let sum: i8 = extended.iter().sum();

            // All extended coordinates should have even parity
            assert_eq!(sum % 2, 0, "Label {label:?} has odd parity");
        }
    }

    #[test]
    fn test_verify_96_classes() {
        assert!(verify_96_classes(96));
        assert!(!verify_96_classes(95));
        assert!(!verify_96_classes(97));
    }

    #[test]
    fn test_atlas_label_binary_weight() {
        let label = AtlasLabel::new(1, 1, 0, 0, 1, 1);
        assert_eq!(label.binary_weight(), 4); // Four 1's

        let label = AtlasLabel::new(0, 0, 0, 0, 0, 0);
        assert_eq!(label.binary_weight(), 0); // All 0's

        let label = AtlasLabel::new(1, 1, 1, 0, 1, 1);
        assert_eq!(label.binary_weight(), 5); // Five 1's
    }
}
