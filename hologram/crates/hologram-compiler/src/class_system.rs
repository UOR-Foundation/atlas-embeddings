//! Atlas 96-Class System (≡₉₆)
//!
//! Implements the authoritative byte → class mapping based on the formal specification.
//!
//! ## Formula
//!
//! ```text
//! class = 24*h₂ + 8*d + ℓ
//! ```
//!
//! Where:
//! - h₂ = (b7<<1) | b6 ∈ {0..3} (scope quadrant)
//! - d = modality from (b4, b5): 00→0, 10→1, 01→2, 11→0
//! - ℓ = (b3<<2)|(b2<<1)|b1 ∈ {0..7} (context slot)

use crate::types::{ClassInfo, Modality, SigilComponents, Transform};

// ============================================================================
// Byte → Components Decoding
// ============================================================================

/// Decode byte to (h₂, d, ℓ) components
///
/// Formula from spec:
/// - h₂ = (b7<<1) | b6 ∈ {0..3}
/// - d₄₅: 0 if (b4,b5)=(0,0); 1 if (1,0); 2 if (0,1); 0 if (1,1)
/// - ℓ = (b3<<2)|(b2<<1)|b1 ∈ {0..7}
///
/// # Example
///
/// ```text
/// use hologram_compiler::decode_byte_to_components;
///
/// let components = decode_byte_to_components(0x2A);
/// assert_eq!(components.h2, 0);
/// assert_eq!(components.d, Modality::Consume);
/// assert_eq!(components.l, 5);
/// ```
pub fn decode_byte_to_components(byte: u8) -> SigilComponents {
    let b7 = (byte >> 7) & 1;
    let b6 = (byte >> 6) & 1;
    let b5 = (byte >> 5) & 1;
    let b4 = (byte >> 4) & 1;
    let b3 = (byte >> 3) & 1;
    let b2 = (byte >> 2) & 1;
    let b1 = (byte >> 1) & 1;

    let h2 = (b7 << 1) | b6;

    let d = match (b4, b5) {
        (0, 0) => Modality::Neutral,
        (1, 0) => Modality::Produce,
        (0, 1) => Modality::Consume,
        (1, 1) => Modality::Neutral, // Falls back to 0 per spec
        _ => unreachable!(),
    };

    let l = (b3 << 2) | (b2 << 1) | b1;

    SigilComponents { h2, d, l }
}

// ============================================================================
// Components → Class Index
// ============================================================================

/// Compute class index from components
///
/// Formula: `class = 24*h₂ + 8*d + ℓ`
///
/// # Example
///
/// ```text
/// use hologram_compiler::{SigilComponents, Modality, components_to_class_index};
///
/// let comp = SigilComponents { h2: 0, d: Modality::Consume, l: 5 };
/// let class_index = components_to_class_index(&comp);
/// assert_eq!(class_index, 21); // 24*0 + 8*2 + 5 = 21
/// ```
pub fn components_to_class_index(comp: &SigilComponents) -> u8 {
    let class = 24 * comp.h2 + 8 * comp.d.as_u8() + comp.l;
    debug_assert!(class < 96);
    class
}

/// Compute class index directly from byte
///
/// # Example
///
/// ```text
/// use hologram_compiler::byte_to_class_index;
///
/// let class_index = byte_to_class_index(0x2A);
/// assert_eq!(class_index, 21);
/// ```
pub fn byte_to_class_index(byte: u8) -> u8 {
    let comp = decode_byte_to_components(byte);
    components_to_class_index(&comp)
}

// ============================================================================
// Class Index → Components
// ============================================================================

/// Decode class index to components
///
/// # Example
///
/// ```text
/// use hologram_compiler::{decode_class_index, Modality};
///
/// let comp = decode_class_index(21);
/// assert_eq!(comp.h2, 0);
/// assert_eq!(comp.d, Modality::Consume);
/// assert_eq!(comp.l, 5);
/// ```
pub fn decode_class_index(class_index: u8) -> SigilComponents {
    assert!(class_index < 96, "Class index {} out of range [0..95]", class_index);

    let h2 = class_index / 24;
    let remainder = class_index % 24;
    let d_val = remainder / 8;
    let l = remainder % 8;

    let d = Modality::from_u8(d_val).expect("Invalid modality");

    SigilComponents { h2, d, l }
}

// ============================================================================
// Components → Canonical Byte
// ============================================================================

/// Encode components to canonical byte (b0=0)
///
/// Maps d={0,1,2} to (b4,b5)={00,10,01}
///
/// # Example
///
/// ```text
/// use hologram_compiler::{SigilComponents, Modality, encode_components_to_byte};
///
/// let comp = SigilComponents { h2: 0, d: Modality::Consume, l: 5 };
/// let byte = encode_components_to_byte(&comp);
/// assert_eq!(byte, 0x2A);
/// ```
pub fn encode_components_to_byte(comp: &SigilComponents) -> u8 {
    let b7 = (comp.h2 >> 1) & 1;
    let b6 = comp.h2 & 1;

    // Map modality to (b4, b5)
    let (b4, b5) = match comp.d {
        Modality::Neutral => (0, 0),
        Modality::Produce => (1, 0),
        Modality::Consume => (0, 1),
    };

    let b3 = (comp.l >> 2) & 1;
    let b2 = (comp.l >> 1) & 1;
    let b1 = comp.l & 1;
    let b0 = 0; // Canonical form

    (b7 << 7) | (b6 << 6) | (b5 << 5) | (b4 << 4) | (b3 << 3) | (b2 << 2) | (b1 << 1) | b0
}

/// Get canonical representative byte for a class index
///
/// # Example
///
/// ```text
/// use hologram_compiler::class_index_to_canonical_byte;
///
/// let byte = class_index_to_canonical_byte(21);
/// assert_eq!(byte, 0x2A);
/// ```
pub fn class_index_to_canonical_byte(class_index: u8) -> u8 {
    let comp = decode_class_index(class_index);
    encode_components_to_byte(&comp)
}

/// Get full class info for a byte
///
/// # Example
///
/// ```text
/// use hologram_compiler::{get_class_info, Modality};
///
/// let info = get_class_info(0x2A);
/// assert_eq!(info.class_index, 21);
/// assert_eq!(info.canonical_byte, 0x2A);
/// assert_eq!(info.components.d, Modality::Consume);
/// ```
pub fn get_class_info(byte: u8) -> ClassInfo {
    let components = decode_byte_to_components(byte);
    let class_index = components_to_class_index(&components);
    let canonical_byte = class_index_to_canonical_byte(class_index);

    ClassInfo {
        class_index,
        components,
        canonical_byte,
    }
}

// ============================================================================
// Transform Operations
// ============================================================================

/// Apply rotation transform R±k (mod 4 on h₂)
///
/// # Example
///
/// ```text
/// use hologram_compiler::{SigilComponents, Modality, apply_rotation};
///
/// let comp = SigilComponents { h2: 0, d: Modality::Neutral, l: 5 };
/// let rotated = apply_rotation(&comp, 1);
/// assert_eq!(rotated.h2, 1);
/// ```
pub fn apply_rotation(comp: &SigilComponents, k: i32) -> SigilComponents {
    let h2 = (((comp.h2 as i32 + k) % 4 + 4) % 4) as u8;
    SigilComponents { h2, ..*comp }
}

/// Apply twist transform T±k (mod 8 on ℓ)
///
/// # Example
///
/// ```text
/// use hologram_compiler::{SigilComponents, Modality, apply_twist};
///
/// let comp = SigilComponents { h2: 0, d: Modality::Neutral, l: 5 };
/// let twisted = apply_twist(&comp, 2);
/// assert_eq!(twisted.l, 7);
/// ```
pub fn apply_twist(comp: &SigilComponents, k: i32) -> SigilComponents {
    let l = (((comp.l as i32 + k) % 8 + 8) % 8) as u8;
    SigilComponents { l, ..*comp }
}

/// Apply mirror transform M (flip modality: 1↔2, 0→0)
///
/// # Example
///
/// ```text
/// use hologram_compiler::{SigilComponents, Modality, apply_mirror};
///
/// let comp = SigilComponents { h2: 0, d: Modality::Produce, l: 5 };
/// let mirrored = apply_mirror(&comp);
/// assert_eq!(mirrored.d, Modality::Consume);
/// ```
pub fn apply_mirror(comp: &SigilComponents) -> SigilComponents {
    let d = match comp.d {
        Modality::Neutral => Modality::Neutral,
        Modality::Produce => Modality::Consume,
        Modality::Consume => Modality::Produce,
    };
    SigilComponents { d, ..*comp }
}

/// Apply scope transform S (permutation from S₁₆)
///
/// Scope transformations act on the (h₂, d) pair via the S₁₆ group:
/// - Rotates h₂ quadrants (mod 4)
/// - Shifts modality (mod 3): I→X→Z→I
///
/// # Example
///
/// ```text
/// use hologram_compiler::{SigilComponents, Modality, apply_scope};
///
/// let comp = SigilComponents { h2: 0, d: Modality::Neutral, l: 5 };
/// let scoped = apply_scope(&comp, 5); // S₁₆ element 5 = (1, 1)
/// assert_eq!(scoped.h2, 1);  // Rotated by 1
/// assert_eq!(scoped.d, Modality::Produce); // Shifted by 1
/// ```
pub fn apply_scope(comp: &SigilComponents, s: u8) -> SigilComponents {
    use crate::automorphism_group::ScopeElement;

    assert!(s < 16, "Scope permutation must be 0..15");

    let scope_elem = ScopeElement::new(s);
    let (h2, d_val) = scope_elem.apply_to_scope(comp.h2, comp.d.as_u8());
    let d = Modality::from_u8(d_val).expect("Invalid modality from scope transformation");

    SigilComponents { h2, d, l: comp.l }
}

/// Apply a complete transform (R, T, M, S)
///
/// Transforms are applied in order: Scope → Rotation → Twist → Mirror
///
/// # Example
///
/// ```text
/// use hologram_compiler::{SigilComponents, Modality, Transform, apply_transforms};
///
/// let comp = SigilComponents { h2: 0, d: Modality::Produce, l: 5 };
/// let transform = Transform::new()
///     .with_scope(1)
///     .with_rotate(1)
///     .with_twist(2)
///     .with_mirror();
/// let transformed = apply_transforms(&comp, &transform);
/// ```
pub fn apply_transforms(comp: &SigilComponents, transform: &Transform) -> SigilComponents {
    let mut result = *comp;

    // Apply scope if present (acts on h₂ and d)
    if let Some(s) = transform.s {
        result = apply_scope(&result, s);
    }

    // Apply rotation if present (acts on h₂)
    if let Some(k) = transform.r {
        result = apply_rotation(&result, k);
    }

    // Apply twist if present (acts on ℓ)
    if let Some(k) = transform.t {
        result = apply_twist(&result, k);
    }

    // Apply mirror if present (acts on d)
    if transform.m {
        result = apply_mirror(&result);
    }

    result
}

// ============================================================================
// Equivalence Testing
// ============================================================================

/// Test if two bytes are in the same equivalence class
///
/// # Example
///
/// ```text
/// use hologram_compiler::equivalent;
///
/// assert!(equivalent(0x00, 0x01)); // Both in class 0
/// assert!(!equivalent(0x00, 0x02)); // Different classes
/// ```
pub fn equivalent(a: u8, b: u8) -> bool {
    byte_to_class_index(a) == byte_to_class_index(b)
}

/// Get all bytes in an equivalence class
///
/// # Example
///
/// ```text
/// use hologram_compiler::equivalence_class;
///
/// let members = equivalence_class(0);
/// assert!(members.contains(&0x00));
/// assert!(members.contains(&0x01));
/// ```
pub fn equivalence_class(class_index: u8) -> Vec<u8> {
    (0..=255u8)
        .filter(|&byte| byte_to_class_index(byte) == class_index)
        .collect()
}

// ============================================================================
// Introspection
// ============================================================================

/// Get all 96 class indices with their canonical bytes
pub fn all_classes() -> Vec<(u8, u8)> {
    (0..96u8)
        .map(|class_index| (class_index, class_index_to_canonical_byte(class_index)))
        .collect()
}

/// Get complete byte→class mapping for all 256 bytes
pub fn byte_class_mapping() -> Vec<(u8, u8)> {
    (0..=255u8).map(|byte| (byte, byte_to_class_index(byte))).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_byte_to_class_basic() {
        // Test case from spec: byte 0x2A → class 21
        let class_index = byte_to_class_index(0x2A);
        assert_eq!(class_index, 21);
    }

    #[test]
    fn test_canonical_byte() {
        // Canonical byte should have LSB = 0
        for class_index in 0..96 {
            let canonical = class_index_to_canonical_byte(class_index);
            assert_eq!(
                canonical & 1,
                0,
                "Class {} canonical byte should have b0=0",
                class_index
            );
        }
    }

    #[test]
    fn test_roundtrip() {
        // Decode → encode should preserve canonical bytes
        for class_index in 0..96 {
            let comp = decode_class_index(class_index);
            let recovered = components_to_class_index(&comp);
            assert_eq!(recovered, class_index);
        }
    }

    #[test]
    fn test_rotation() {
        let comp = SigilComponents {
            h2: 0,
            d: Modality::Neutral,
            l: 0,
        };
        let rotated = apply_rotation(&comp, 1);
        assert_eq!(rotated.h2, 1);

        // Test wrap-around
        let rotated = apply_rotation(&comp, 4);
        assert_eq!(rotated.h2, 0);

        // Test negative
        let rotated = apply_rotation(&comp, -1);
        assert_eq!(rotated.h2, 3);
    }

    #[test]
    fn test_twist() {
        let comp = SigilComponents {
            h2: 0,
            d: Modality::Neutral,
            l: 5,
        };
        let twisted = apply_twist(&comp, 2);
        assert_eq!(twisted.l, 7);

        // Test wrap-around
        let twisted = apply_twist(&comp, 3);
        assert_eq!(twisted.l, 0);

        // Test negative
        let twisted = apply_twist(&comp, -1);
        assert_eq!(twisted.l, 4);
    }

    #[test]
    fn test_mirror() {
        let comp = SigilComponents {
            h2: 0,
            d: Modality::Produce,
            l: 0,
        };
        let mirrored = apply_mirror(&comp);
        assert_eq!(mirrored.d, Modality::Consume);

        // Test neutral stays neutral
        let comp = SigilComponents {
            h2: 0,
            d: Modality::Neutral,
            l: 0,
        };
        let mirrored = apply_mirror(&comp);
        assert_eq!(mirrored.d, Modality::Neutral);
    }

    #[test]
    fn test_equivalence() {
        // Bytes differing only in b0 should be equivalent
        assert!(equivalent(0x00, 0x01));
        assert!(equivalent(0x02, 0x03));

        // Bytes with different class components should not be equivalent
        assert!(!equivalent(0x00, 0x02));
    }

    #[test]
    fn test_all_classes() {
        let classes = all_classes();
        assert_eq!(classes.len(), 96);

        // All class indices should be unique
        let indices: Vec<u8> = classes.iter().map(|(idx, _)| *idx).collect();
        let mut sorted = indices.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(sorted.len(), 96);
    }

    #[test]
    fn test_scope_identity() {
        // Scope permutation 0 should be identity
        let comp = SigilComponents {
            h2: 1,
            d: Modality::Produce,
            l: 5,
        };
        let scoped = apply_scope(&comp, 0);
        assert_eq!(scoped.h2, comp.h2);
        assert_eq!(scoped.d, comp.d);
        assert_eq!(scoped.l, comp.l);
    }

    #[test]
    fn test_scope_quadrant_rotation() {
        // Scope element (1, 0) = index 4: rotates h₂ by 1
        let comp = SigilComponents {
            h2: 0,
            d: Modality::Neutral,
            l: 5,
        };
        let scoped = apply_scope(&comp, 4); // (1, 0)
        assert_eq!(scoped.h2, 1);
        assert_eq!(scoped.d, Modality::Neutral);
        assert_eq!(scoped.l, 5);
    }

    #[test]
    fn test_scope_modality_shift() {
        // Scope element (0, 1) = index 1: shifts d by 1
        let comp = SigilComponents {
            h2: 0,
            d: Modality::Neutral, // 0
            l: 5,
        };
        let scoped = apply_scope(&comp, 1); // (0, 1)
        assert_eq!(scoped.h2, 0);
        assert_eq!(scoped.d, Modality::Produce); // 1
        assert_eq!(scoped.l, 5);

        // Test modality wrap: 2 + 1 = 0 (mod 3)
        let comp2 = SigilComponents {
            h2: 0,
            d: Modality::Consume, // 2
            l: 5,
        };
        let scoped2 = apply_scope(&comp2, 1);
        assert_eq!(scoped2.d, Modality::Neutral); // (2+1) % 3 = 0
    }

    #[test]
    fn test_scope_combined() {
        // Scope element (2, 1) = index 9: h₂+2, d+1
        let comp = SigilComponents {
            h2: 1,
            d: Modality::Neutral, // 0
            l: 5,
        };
        let scoped = apply_scope(&comp, 9); // (2, 1)
        assert_eq!(scoped.h2, 3); // (1+2) % 4 = 3
        assert_eq!(scoped.d, Modality::Produce); // (0+1) % 3 = 1
        assert_eq!(scoped.l, 5);
    }

    #[test]
    fn test_apply_transforms_with_scope() {
        let comp = SigilComponents {
            h2: 0,
            d: Modality::Neutral,
            l: 0,
        };

        // Apply scope transformation
        let transform = Transform::new().with_scope(5); // (1, 1)
        let result = apply_transforms(&comp, &transform);
        assert_eq!(result.h2, 1); // h₂ + 1
        assert_eq!(result.d, Modality::Produce); // d + 1

        // Apply scope + rotation
        let transform2 = Transform::new().with_scope(4).with_rotate(1); // S: h₂+1, R: h₂+1
        let result2 = apply_transforms(&comp, &transform2);
        assert_eq!(result2.h2, 2); // 0 + 1 (scope) + 1 (rotate) = 2
    }

    #[test]
    fn test_apply_transforms_order() {
        // Test that transforms are applied in the right order: S → R → T → M
        let comp = SigilComponents {
            h2: 0,
            d: Modality::Neutral,
            l: 0,
        };

        let transform = Transform::new()
            .with_scope(1) // (0, 1): d = 0 → 1 (Produce)
            .with_mirror(); // flip: 1 → 2 (Consume)

        let result = apply_transforms(&comp, &transform);
        assert_eq!(result.d, Modality::Consume); // 0 → 1 (scope) → 2 (mirror)
    }

    #[test]
    fn test_transform_combine_with_scope() {
        use crate::automorphism_group::ScopeElement;

        let t1 = Transform::new().with_scope(5); // (1, 1)
        let t2 = Transform::new().with_scope(6); // (1, 2)

        let combined = t1.combine(&t2);

        // (1,1) ∘ (1,2) = ((1+1)%4, (1+2)%4) = (2, 3)
        // Index = 4*2 + 3 = 11
        assert_eq!(combined.s, Some(11));

        // Verify via ScopeElement
        let s1 = ScopeElement::new(5);
        let s2 = ScopeElement::new(6);
        let composed = s1.compose(s2);
        assert_eq!(composed.permutation_index, 11);
    }

    #[test]
    fn test_scope_preserves_context() {
        // Scope should not affect ℓ (context)
        for s in 0..16u8 {
            for l in 0..8u8 {
                let comp = SigilComponents {
                    h2: 0,
                    d: Modality::Neutral,
                    l,
                };
                let scoped = apply_scope(&comp, s);
                assert_eq!(scoped.l, l, "Scope {} should preserve context {}", s, l);
            }
        }
    }

    #[test]
    fn test_all_scope_permutations_valid() {
        // All 16 scope permutations should produce valid results
        for s in 0..16u8 {
            for h2 in 0..4u8 {
                for d_val in 0..3u8 {
                    let d = Modality::from_u8(d_val).unwrap();
                    let comp = SigilComponents { h2, d, l: 0 };
                    let scoped = apply_scope(&comp, s);

                    // Results should be in valid ranges
                    assert!(scoped.h2 < 4, "h₂ out of range for scope {}", s);
                    assert!(scoped.d.as_u8() < 3, "d out of range for scope {}", s);
                }
            }
        }
    }
}
