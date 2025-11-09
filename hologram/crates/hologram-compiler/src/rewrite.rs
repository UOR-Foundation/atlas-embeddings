//! Rewrite Engine for Canonicalization
//!
//! Applies pattern-based rewrite rules to simplify expressions.

use crate::ast::{Parallel, Phrase, Sequential};
use crate::rules::RuleSet;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// Result of a rewrite operation
#[derive(Debug, Clone)]
pub struct RewriteResult {
    /// The rewritten phrase
    pub phrase: Phrase,
    /// Whether any rewrite was applied
    pub changed: bool,
    /// Number of rewrites applied
    pub rewrite_count: usize,
    /// Names of rules that were applied
    pub applied_rules: Vec<String>,
}

/// Rewrite engine
pub struct RewriteEngine {
    rules: RuleSet,
    max_iterations: usize,
}

impl RewriteEngine {
    /// Create a new rewrite engine with standard rules
    pub fn new() -> Self {
        RewriteEngine {
            rules: RuleSet::standard(),
            max_iterations: 100,
        }
    }

    /// Create with custom rules
    pub fn with_rules(rules: RuleSet) -> Self {
        RewriteEngine {
            rules,
            max_iterations: 100,
        }
    }

    /// Set maximum iterations for convergence
    pub fn with_max_iterations(mut self, max: usize) -> Self {
        self.max_iterations = max;
        self
    }

    /// Apply a single rewrite pass to a sequential expression
    /// Returns (rewritten_seq, changed, rule_name)
    fn apply_single_pass(&self, seq: &Sequential) -> (Sequential, bool, Option<String>) {
        // Try each rule in order
        for rule in self.rules.rules() {
            if let Some(position) = rule.pattern.find_first(seq) {
                // Found a match, apply the replacement
                let mut new_items = Vec::new();

                // Add items before match
                new_items.extend_from_slice(&seq.items[0..position]);

                // Add replacement items
                new_items.extend_from_slice(&rule.replacement.items);

                // Add items after match
                let end = position + rule.pattern.len();
                new_items.extend_from_slice(&seq.items[end..]);

                return (Sequential::new(new_items), true, Some(rule.name.clone()));
            }
        }

        // No rewrites applied
        (seq.clone(), false, None)
    }

    /// Flatten groups in a sequential expression by expanding them into operations
    /// Groups containing single-branch parallels are flattened into their sequential operations
    fn flatten_groups(&self, seq: &Sequential) -> Sequential {
        let mut flattened = Vec::new();

        for term in &seq.items {
            match term {
                crate::ast::Term::Group(par) => {
                    // If the group contains a single branch, flatten it
                    if par.branches.len() == 1 {
                        // Directly flatten the branch's items
                        flattened.extend(par.branches[0].items.clone());
                    } else {
                        // Multi-branch group, keep as-is (can't flatten)
                        flattened.push(term.clone());
                    }
                }
                _ => flattened.push(term.clone()),
            }
        }

        Sequential::new(flattened)
    }

    /// Apply rewrites to a sequential expression until convergence
    pub fn rewrite_sequential(&self, seq: &Sequential) -> RewriteResult {
        // First, flatten any groups
        let mut current = self.flatten_groups(seq);
        let mut total_changes = 0;
        let mut applied_rules = Vec::new();

        for _ in 0..self.max_iterations {
            let (new_seq, changed, rule_name) = self.apply_single_pass(&current);

            if !changed {
                // Converged
                break;
            }

            current = new_seq;
            total_changes += 1;

            if let Some(name) = rule_name {
                applied_rules.push(name);
            }
        }

        // Wrap in a phrase
        let phrase = Phrase::Parallel(Parallel::single(current));

        RewriteResult {
            phrase,
            changed: total_changes > 0,
            rewrite_count: total_changes,
            applied_rules,
        }
    }

    /// Apply rewrites to a parallel expression
    ///
    /// Note: Currently unused, reserved for future parallel optimization
    #[allow(dead_code)]
    fn rewrite_parallel(&self, par: &Parallel) -> Parallel {
        let rewritten_branches = par
            .branches
            .iter()
            .map(|branch| {
                let result = self.rewrite_sequential(branch);
                match result.phrase {
                    Phrase::Parallel(p) => p.branches.into_iter().next().unwrap_or(branch.clone()),
                    Phrase::Transformed { body, .. } => body.branches.into_iter().next().unwrap_or(branch.clone()),
                }
            })
            .collect();

        Parallel::new(rewritten_branches)
    }

    /// Apply rewrites to a complete phrase
    pub fn rewrite(&self, phrase: &Phrase) -> RewriteResult {
        match phrase {
            Phrase::Parallel(par) => {
                let mut total_changes = 0;
                let mut all_applied_rules = Vec::new();

                let rewritten_par = Parallel::new(
                    par.branches
                        .iter()
                        .map(|branch| {
                            let result = self.rewrite_sequential(branch);
                            total_changes += result.rewrite_count;
                            all_applied_rules.extend(result.applied_rules);

                            match result.phrase {
                                Phrase::Parallel(p) => p.branches.into_iter().next().unwrap_or(branch.clone()),
                                Phrase::Transformed { body, .. } => {
                                    body.branches.into_iter().next().unwrap_or(branch.clone())
                                }
                            }
                        })
                        .collect(),
                );

                RewriteResult {
                    phrase: Phrase::Parallel(rewritten_par),
                    changed: total_changes > 0,
                    rewrite_count: total_changes,
                    applied_rules: all_applied_rules,
                }
            }

            Phrase::Transformed { transform, body } => {
                let mut total_changes = 0;
                let mut all_applied_rules = Vec::new();

                let rewritten_par = Parallel::new(
                    body.branches
                        .iter()
                        .map(|branch| {
                            let result = self.rewrite_sequential(branch);
                            total_changes += result.rewrite_count;
                            all_applied_rules.extend(result.applied_rules);

                            match result.phrase {
                                Phrase::Parallel(p) => p.branches.into_iter().next().unwrap_or(branch.clone()),
                                Phrase::Transformed { body, .. } => {
                                    body.branches.into_iter().next().unwrap_or(branch.clone())
                                }
                            }
                        })
                        .collect(),
                );

                RewriteResult {
                    phrase: Phrase::Transformed {
                        transform: *transform,
                        body: Box::new(rewritten_par),
                    },
                    changed: total_changes > 0,
                    rewrite_count: total_changes,
                    applied_rules: all_applied_rules,
                }
            }
        }
    }
}

impl Default for RewriteEngine {
    fn default() -> Self {
        Self::new()
    }
}

/// Compute hash of a phrase for convergence detection
pub fn phrase_hash(phrase: &Phrase) -> u64 {
    let mut hasher = DefaultHasher::new();
    format!("{:?}", phrase).hash(&mut hasher);
    hasher.finish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Term;
    use crate::parser::parse;

    #[test]
    fn test_rewrite_h_squared() {
        let engine = RewriteEngine::new();

        // H² = copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21
        let phrase = parse("copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21").unwrap();

        let result = engine.rewrite(&phrase);

        assert!(result.changed, "H² should be rewritten");
        assert_eq!(result.rewrite_count, 1);
        assert!(result.applied_rules.contains(&"H² = I".to_string()));

        // Result should be mark@c00 (identity)
        match &result.phrase {
            Phrase::Parallel(par) => {
                assert_eq!(par.branches.len(), 1);
                assert_eq!(par.branches[0].items.len(), 1);

                match &par.branches[0].items[0] {
                    Term::Operation { generator, target } => {
                        assert_eq!(*generator, crate::types::Generator::Mark);
                        if let crate::types::ClassTarget::Single(sigil) = target {
                            assert_eq!(sigil.class_index, 0);
                        }
                    }
                    _ => panic!("Expected operation"),
                }
            }
            _ => panic!("Expected parallel phrase"),
        }
    }

    #[test]
    fn test_rewrite_x_squared() {
        let engine = RewriteEngine::new();

        // X² = mark@c21 . mark@c21
        let phrase = parse("mark@c21 . mark@c21").unwrap();

        let result = engine.rewrite(&phrase);

        assert!(result.changed, "X² should be rewritten");
        assert_eq!(result.rewrite_count, 1);
        assert!(result.applied_rules.contains(&"X² = I".to_string()));
    }

    #[test]
    fn test_rewrite_h_fourth() {
        let engine = RewriteEngine::new();

        // H⁴ = H² . H²
        // copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21
        let phrase = parse(
            "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21 . \
             copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21",
        )
        .unwrap();

        let result = engine.rewrite(&phrase);

        assert!(result.changed, "H⁴ should be rewritten");
        // Should apply H²→I twice, then I.I→I
        assert!(result.rewrite_count >= 2, "Should have multiple rewrites");
    }

    #[test]
    fn test_no_rewrite() {
        let engine = RewriteEngine::new();

        // Single operation, no rewrites apply
        let phrase = parse("mark@c42").unwrap();

        let result = engine.rewrite(&phrase);

        assert!(!result.changed, "Single operation should not be rewritten");
        assert_eq!(result.rewrite_count, 0);
    }

    #[test]
    fn test_identity_composition() {
        let engine = RewriteEngine::new();

        // I.I = mark@c00 . mark@c00
        let phrase = parse("mark@c00 . mark@c00").unwrap();

        let result = engine.rewrite(&phrase);

        assert!(result.changed, "I.I should be rewritten");
        assert_eq!(result.rewrite_count, 1);
        assert!(result.applied_rules.contains(&"I.I = I".to_string()));
    }

    #[test]
    fn test_convergence() {
        let engine = RewriteEngine::new();

        // Complex expression that requires multiple iterations
        // H² . I → I . I → I
        let phrase = parse("copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21 . mark@c00").unwrap();

        let result = engine.rewrite(&phrase);

        assert!(result.changed);
        assert!(result.rewrite_count >= 1);
    }

    #[test]
    fn test_parallel_branches() {
        let engine = RewriteEngine::new();

        // Parallel: H² || X² (without grouping)
        let phrase = parse(
            "copy@c05->c06 . mark@c21 . copy@c05->c06 . mark@c21 || \
             mark@c21 . mark@c21",
        )
        .unwrap();

        let result = engine.rewrite(&phrase);

        assert!(result.changed, "Both branches should be rewritten");
        // Should rewrite both H² and X²
        assert!(result.rewrite_count >= 2);
    }

    #[test]
    fn test_phrase_hash_same() {
        let phrase1 = parse("mark@c21").unwrap();
        let phrase2 = parse("mark@c21").unwrap();

        let hash1 = phrase_hash(&phrase1);
        let hash2 = phrase_hash(&phrase2);

        assert_eq!(hash1, hash2, "Identical phrases should have same hash");
    }

    #[test]
    fn test_phrase_hash_different() {
        let phrase1 = parse("mark@c21").unwrap();
        let phrase2 = parse("mark@c42").unwrap();

        let hash1 = phrase_hash(&phrase1);
        let hash2 = phrase_hash(&phrase2);

        assert_ne!(hash1, hash2, "Different phrases should have different hashes");
    }
}
