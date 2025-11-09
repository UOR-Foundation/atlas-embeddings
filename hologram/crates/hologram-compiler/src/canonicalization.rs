//! Canonicalization Engine
//!
//! Provides canonicalization of sigil expressions through pattern-based rewriting.
//! This is a pure compilation feature used by the compiler to optimize circuits.

use crate::ast::Phrase;
use crate::parser::{parse, ParseError};
use crate::rewrite::{RewriteEngine, RewriteResult};

/// Canonicalization interface for sigil expressions
pub struct Canonicalizer;

impl Canonicalizer {
    /// Parse and canonicalize an expression
    ///
    /// Returns the rewrite result including:
    /// - Canonical phrase
    /// - Whether any rewrites were applied
    /// - Number of rewrites
    /// - Names of applied rules
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::Canonicalizer;
    ///
    /// // H² should canonicalize to I
    /// let result = Canonicalizer::parse_and_canonicalize(
    ///     "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21"
    /// ).unwrap();
    ///
    /// assert!(result.changed);
    /// assert!(result.rewrite_count >= 1);
    /// assert!(result.applied_rules.contains(&"H² = I".to_string()));
    /// ```
    pub fn parse_and_canonicalize(expression: &str) -> Result<RewriteResult, ParseError> {
        let phrase = parse(expression)?;
        Ok(Self::canonicalize(&phrase))
    }

    /// Get canonical form of an expression as a string
    ///
    /// Returns a human-readable representation of the canonical form.
    ///
    /// # Example
    ///
    /// ```
    /// use hologram_compiler::Canonicalizer;
    ///
    /// let canonical = Canonicalizer::canonical_form(
    ///     "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21"
    /// ).unwrap();
    ///
    /// // H² canonicalizes to I (Mark generator, class_index: 0)
    /// assert!(canonical.contains("Mark"));
    /// assert!(canonical.contains("class_index: 0"));
    /// ```
    pub fn canonical_form(expression: &str) -> Result<String, ParseError> {
        let result = Self::parse_and_canonicalize(expression)?;
        Ok(format!("{:?}", result.phrase))
    }

    /// Internal: Apply canonicalization rewrites to a phrase
    fn canonicalize(phrase: &Phrase) -> RewriteResult {
        let engine = RewriteEngine::new();
        engine.rewrite(phrase)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_h_squared_canonicalization() {
        // H² should canonicalize to I
        let result =
            Canonicalizer::parse_and_canonicalize("copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21").unwrap();

        assert!(result.changed, "H² should be rewritten");
        assert_eq!(result.rewrite_count, 1);
        assert!(result.applied_rules.contains(&"H² = I".to_string()));
    }

    #[test]
    fn test_x_squared_canonicalization() {
        // X² should canonicalize to I
        let result = Canonicalizer::parse_and_canonicalize("mark@c21 . mark@c21").unwrap();

        assert!(result.changed, "X² should be rewritten");
        assert_eq!(result.rewrite_count, 1);
        assert!(result.applied_rules.contains(&"X² = I".to_string()));
    }

    #[test]
    fn test_canonical_form() {
        let canonical = Canonicalizer::canonical_form("copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21").unwrap();

        // Should contain Mark (generator enum variant)
        // and class_index: 0 (identity)
        assert!(canonical.contains("Mark"));
        assert!(canonical.contains("class_index: 0"));
    }

    #[test]
    fn test_h_fourth_canonicalization() {
        // H⁴ = (H²)² = I² = I
        let result = Canonicalizer::parse_and_canonicalize(
            "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21 . \
             copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21",
        )
        .unwrap();

        assert!(result.changed);
        assert!(result.rewrite_count >= 2, "Should have multiple rewrites");
    }

    #[test]
    fn test_parallel_canonicalization() {
        // Both branches should canonicalize
        let result = Canonicalizer::parse_and_canonicalize(
            "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21 || \
             mark@c21 . mark@c21",
        )
        .unwrap();

        assert!(result.changed);
        assert!(result.rewrite_count >= 2, "Both branches should be rewritten");
    }

    #[test]
    fn test_identity_composition() {
        // I.I = I
        let result = Canonicalizer::parse_and_canonicalize("mark@c00 . mark@c00").unwrap();
        assert!(result.changed);
        assert!(result.applied_rules.contains(&"I.I = I".to_string()));
    }
}
