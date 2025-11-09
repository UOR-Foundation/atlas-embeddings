//! The Seven Fundamental Generators
//!
//! The Atlas Sigil Algebra is built on seven primitive operations:
//!
//! 1. **mark** - Introduce/remove distinction
//! 2. **copy** - Comultiplication (fan-out)
//! 3. **swap** - Symmetry/braid operation
//! 4. **merge** - Fold/meet operation
//! 5. **split** - Case analysis/deconstruct
//! 6. **quote** - Suspend computation
//! 7. **evaluate** - Force/discharge thunk
//!
//! In the literal backend, all generators produce the same canonical byte
//! for a given class sigil. The generator name affects only the operational
//! backend (word semantics).

use crate::types::Generator;

/// Get operational word for a generator with modality annotation
///
/// # Example
///
/// ```text
/// use hologram_compiler::{Generator, Modality, generator_word};
///
/// let word = generator_word(Generator::Copy, Modality::Neutral);
/// assert_eq!(word, "copy[d=0]");
/// ```
pub fn generator_word(gen: Generator, modality: u8) -> String {
    format!("{}[d={}]", gen.as_str(), modality)
}

/// Get phase word for a scope quadrant
///
/// # Example
///
/// ```text
/// use hologram_compiler::phase_word;
///
/// let word = phase_word(0);
/// assert_eq!(word, "phase[h₂=0]");
/// ```
pub fn phase_word(h2: u8) -> String {
    format!("phase[h₂={}]", h2)
}

/// Generator descriptions for documentation
pub fn generator_description(gen: Generator) -> &'static str {
    match gen {
        Generator::Mark => "Introduce or remove distinction in the resonance field",
        Generator::Copy => "Comultiplication - fan out a value to multiple contexts",
        Generator::Swap => "Symmetric braid - exchange two values in resonance space",
        Generator::Merge => "Fold operation - combine two contexts into one",
        Generator::Split => "Case analysis - deconstruct a value into components",
        Generator::Quote => "Suspend computation - create a deferred thunk",
        Generator::Evaluate => "Force evaluation - discharge a suspended thunk",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Modality;

    #[test]
    fn test_generator_word() {
        let word = generator_word(Generator::Copy, Modality::Neutral.as_u8());
        assert_eq!(word, "copy[d=0]");

        let word = generator_word(Generator::Merge, Modality::Produce.as_u8());
        assert_eq!(word, "merge[d=1]");
    }

    #[test]
    fn test_phase_word() {
        assert_eq!(phase_word(0), "phase[h₂=0]");
        assert_eq!(phase_word(3), "phase[h₂=3]");
    }

    #[test]
    fn test_all_generators() {
        for gen in [
            Generator::Mark,
            Generator::Copy,
            Generator::Swap,
            Generator::Merge,
            Generator::Split,
            Generator::Quote,
            Generator::Evaluate,
        ] {
            let desc = generator_description(gen);
            assert!(!desc.is_empty());
        }
    }
}
