//! Rewrite Rules for Canonicalization
//!
//! Implements quantum gate identities and simplification rules.

use crate::ast::{Sequential, Term};
use crate::pattern::{Pattern, PatternElement};
use crate::types::{ClassSigil, ClassTarget, Generator};

/// A rewrite rule: pattern → replacement
#[derive(Debug, Clone)]
pub struct RewriteRule {
    /// Pattern to match
    pub pattern: Pattern,
    /// Replacement sequence
    pub replacement: Sequential,
    /// Rule name/description
    pub name: String,
    /// Rule priority (higher = applied first)
    pub priority: u32,
}

impl RewriteRule {
    pub fn new(pattern: Pattern, replacement: Sequential, name: impl Into<String>) -> Self {
        RewriteRule {
            pattern,
            replacement,
            name: name.into(),
            priority: 50, // Default medium priority
        }
    }

    pub fn with_priority(pattern: Pattern, replacement: Sequential, name: impl Into<String>, priority: u32) -> Self {
        RewriteRule {
            pattern,
            replacement,
            name: name.into(),
            priority,
        }
    }
}

/// Standard quantum gate identity rules
pub fn standard_rules() -> Vec<RewriteRule> {
    vec![
        // ========================================
        // SELF-INVERSE GATES
        // ========================================

        // ========================================
        // CONJUGATION RULES (HIGHEST PRIORITY)
        // ========================================
        // These must be tried BEFORE simpler patterns that match subsets

        // HXH = Z (Conjugating X by H gives Z)
        // (copy@c05 . mark@c21) . mark@c21 . (copy@c05 . mark@c21) → mark@c42
        // PRIORITY: 100 (highest) - must match before X² pattern
        RewriteRule::with_priority(
            Pattern::new(
                vec![
                    PatternElement::exact(Generator::Copy, 5),
                    PatternElement::exact(Generator::Mark, 21),
                    PatternElement::exact(Generator::Mark, 21),
                    PatternElement::exact(Generator::Copy, 5),
                    PatternElement::exact(Generator::Mark, 21),
                ],
                "HXH pattern",
            ),
            Sequential::new(vec![Term::Operation {
                generator: Generator::Mark,
                target: ClassTarget::Single(ClassSigil::new(42).unwrap()), // Z gate
            }]),
            "HXH = Z",
            100, // Highest priority - longest, most specific pattern
        ),
        // ========================================
        // SELF-INVERSE GATES (MEDIUM PRIORITY)
        // ========================================

        // H² = I (Hadamard squared equals identity)
        // H = copy@c05 . mark@c21
        // H² = (copy@c05 . mark@c21) . (copy@c05 . mark@c21) → mark@c00
        // PRIORITY: 50 (default medium)
        RewriteRule::new(
            Pattern::new(
                vec![
                    PatternElement::exact(Generator::Copy, 5),
                    PatternElement::exact(Generator::Mark, 21),
                    PatternElement::exact(Generator::Copy, 5),
                    PatternElement::exact(Generator::Mark, 21),
                ],
                "H² pattern",
            ),
            Sequential::new(vec![Term::Operation {
                generator: Generator::Mark,
                target: ClassTarget::Single(ClassSigil::new(0).unwrap()), // Identity
            }]),
            "H² = I",
        ),
        // ========================================
        // SIMPLE PAULI RULES (LOW PRIORITY)
        // ========================================
        // These are simple 2-element patterns, try them last

        // X² = I (Pauli-X squared equals identity)
        // X = mark@c21
        // X² = mark@c21 . mark@c21 → mark@c00
        // PRIORITY: 10 (low) - simple pattern, try after complex ones
        RewriteRule::with_priority(
            Pattern::new(
                vec![
                    PatternElement::exact(Generator::Mark, 21),
                    PatternElement::exact(Generator::Mark, 21),
                ],
                "X² pattern",
            ),
            Sequential::new(vec![Term::Operation {
                generator: Generator::Mark,
                target: ClassTarget::Single(ClassSigil::new(0).unwrap()),
            }]),
            "X² = I",
            10, // Low priority - simple pattern
        ),
        // Z² = I (Pauli-Z squared equals identity)
        // Z = mark@c42 (assuming this mapping)
        // Z² = mark@c42 . mark@c42 → mark@c00
        // PRIORITY: 10 (low)
        RewriteRule::with_priority(
            Pattern::new(
                vec![
                    PatternElement::exact(Generator::Mark, 42),
                    PatternElement::exact(Generator::Mark, 42),
                ],
                "Z² pattern",
            ),
            Sequential::new(vec![Term::Operation {
                generator: Generator::Mark,
                target: ClassTarget::Single(ClassSigil::new(0).unwrap()),
            }]),
            "Z² = I",
            10, // Low priority - simple pattern
        ),
        // ========================================
        // IDENTITY RULES (LOWEST PRIORITY)
        // ========================================

        // I.I = I (Identity composition)
        // mark@c00 . mark@c00 → mark@c00
        // PRIORITY: 5 (lowest) - only apply to clean up remaining identities
        RewriteRule::with_priority(
            Pattern::new(
                vec![
                    PatternElement::exact(Generator::Mark, 0),
                    PatternElement::exact(Generator::Mark, 0),
                ],
                "I.I pattern",
            ),
            Sequential::new(vec![Term::Operation {
                generator: Generator::Mark,
                target: ClassTarget::Single(ClassSigil::new(0).unwrap()),
            }]),
            "I.I = I",
            5, // Lowest priority - cleanup rule
        ),
        // ========================================
        // PHASE GATE RULES (LOW PRIORITY)
        // ========================================

        // S² = Z (Phase gate squared equals Z)
        // S = mark@c07 (assuming this mapping)
        // S² = mark@c07 . mark@c07 → mark@c42
        // PRIORITY: 10 (low)
        RewriteRule::with_priority(
            Pattern::new(
                vec![
                    PatternElement::exact(Generator::Mark, 7),
                    PatternElement::exact(Generator::Mark, 7),
                ],
                "S² pattern",
            ),
            Sequential::new(vec![Term::Operation {
                generator: Generator::Mark,
                target: ClassTarget::Single(ClassSigil::new(42).unwrap()), // Z gate
            }]),
            "S² = Z",
            10, // Low priority - simple pattern
        ),
    ]
}

/// Build a RuleSet from rules
pub struct RuleSet {
    rules: Vec<RewriteRule>,
}

impl RuleSet {
    /// Create a new rule set
    /// Rules are automatically sorted by priority (highest first)
    pub fn new(mut rules: Vec<RewriteRule>) -> Self {
        // Sort by priority (highest first)
        rules.sort_by(|a, b| b.priority.cmp(&a.priority));
        RuleSet { rules }
    }

    /// Create standard quantum gate rule set
    /// Rules are automatically sorted by priority (highest first)
    pub fn standard() -> Self {
        RuleSet::new(standard_rules())
    }

    /// Get all rules
    pub fn rules(&self) -> &[RewriteRule] {
        &self.rules
    }

    /// Add a rule
    pub fn add_rule(&mut self, rule: RewriteRule) {
        self.rules.push(rule);
    }

    /// Get number of rules
    pub fn len(&self) -> usize {
        self.rules.len()
    }

    /// Check if rule set is empty
    pub fn is_empty(&self) -> bool {
        self.rules.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_standard_rules_count() {
        let rules = standard_rules();
        assert!(rules.len() >= 5, "Should have at least 5 standard rules");
    }

    #[test]
    fn test_rule_set_creation() {
        let rule_set = RuleSet::standard();
        assert!(rule_set.len() >= 5);
    }

    #[test]
    fn test_h_squared_rule() {
        let rules = standard_rules();
        let h_squared = rules.iter().find(|r| r.name == "H² = I").unwrap();

        // Pattern should be 4 elements (copy, mark, copy, mark)
        assert_eq!(h_squared.pattern.len(), 4);

        // Replacement should be 1 element (identity)
        assert_eq!(h_squared.replacement.items.len(), 1);

        // Verify replacement is mark@c00 (identity)
        match &h_squared.replacement.items[0] {
            Term::Operation { generator, target } => {
                assert_eq!(*generator, Generator::Mark);
                if let ClassTarget::Single(sigil) = target {
                    assert_eq!(sigil.class_index, 0);
                }
            }
            _ => panic!("Expected operation"),
        }
    }

    #[test]
    fn test_x_squared_rule() {
        let rules = standard_rules();
        let x_squared = rules.iter().find(|r| r.name == "X² = I").unwrap();

        // Pattern should be 2 elements (mark, mark)
        assert_eq!(x_squared.pattern.len(), 2);

        // Both should be mark@c21
        match &x_squared.pattern.elements[0] {
            PatternElement::Exact { generator, class } => {
                assert_eq!(*generator, Generator::Mark);
                assert_eq!(*class, 21);
            }
            _ => panic!("Expected exact pattern"),
        }
    }

    #[test]
    fn test_identity_rule() {
        let rules = standard_rules();
        let identity = rules.iter().find(|r| r.name == "I.I = I").unwrap();

        assert_eq!(identity.pattern.len(), 2);
        assert_eq!(identity.replacement.items.len(), 1);
    }

    #[test]
    fn test_hxh_rule() {
        let rules = standard_rules();
        let hxh = rules.iter().find(|r| r.name == "HXH = Z").unwrap();

        // Pattern should be 5 elements (H, X, H)
        assert_eq!(hxh.pattern.len(), 5);

        // Replacement should be mark@c42 (Z gate)
        match &hxh.replacement.items[0] {
            Term::Operation { generator, target } => {
                assert_eq!(*generator, Generator::Mark);
                if let ClassTarget::Single(sigil) = target {
                    assert_eq!(sigil.class_index, 42);
                }
            }
            _ => panic!("Expected operation"),
        }
    }

    #[test]
    fn test_all_rules_have_replacement() {
        let rules = standard_rules();
        for rule in rules {
            assert!(
                !rule.replacement.items.is_empty(),
                "Rule '{}' has empty replacement",
                rule.name
            );
        }
    }

    #[test]
    fn test_all_rules_have_pattern() {
        let rules = standard_rules();
        for rule in rules {
            assert!(!rule.pattern.is_empty(), "Rule '{}' has empty pattern", rule.name);
        }
    }
}
