//! Pattern Matching Engine for Rewrite Rules
//!
//! Supports matching sequences of operations for canonicalization.

use crate::ast::{Sequential, Term};
use crate::types::Generator;

/// A pattern element for matching
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PatternElement {
    /// Exact match: specific generator and class
    Exact { generator: Generator, class: u8 },
    /// Generator match: specific generator, any class
    AnyClass { generator: Generator },
    /// Wildcard: matches any single operation
    Any,
}

impl PatternElement {
    /// Create exact pattern element
    pub fn exact(generator: Generator, class: u8) -> Self {
        PatternElement::Exact { generator, class }
    }

    /// Create any-class pattern element
    pub fn any_class(generator: Generator) -> Self {
        PatternElement::AnyClass { generator }
    }

    /// Create wildcard pattern element
    pub fn any() -> Self {
        PatternElement::Any
    }

    /// Check if this pattern element matches a term
    pub fn matches(&self, term: &Term) -> bool {
        match (self, term) {
            (PatternElement::Any, Term::Operation { .. }) => true,

            (PatternElement::AnyClass { generator: pat_gen }, Term::Operation { generator, .. }) => {
                pat_gen == generator
            }

            (
                PatternElement::Exact {
                    generator: pat_gen,
                    class: pat_class,
                },
                Term::Operation { generator, target },
            ) => {
                let class_index = match target {
                    crate::types::ClassTarget::Single(sigil) => sigil.class_index,
                    crate::types::ClassTarget::Range(_) => return false, // Ranges don't match patterns yet
                    // For CopyPair, match against source class
                    crate::types::ClassTarget::CopyPair { src, .. } => src.class_index,
                    // For SwapPair, match against first class
                    crate::types::ClassTarget::SwapPair { a, .. } => a.class_index,
                    // For TripleClass (merge/split), match against primary class
                    crate::types::ClassTarget::TripleClass { primary, .. } => primary.class_index,
                };
                pat_gen == generator && *pat_class == class_index
            }

            _ => false,
        }
    }
}

/// A pattern: sequence of pattern elements
#[derive(Debug, Clone)]
pub struct Pattern {
    pub elements: Vec<PatternElement>,
    pub description: String,
}

impl Pattern {
    /// Create a new pattern
    pub fn new(elements: Vec<PatternElement>, description: impl Into<String>) -> Self {
        Pattern {
            elements,
            description: description.into(),
        }
    }

    /// Get pattern length
    pub fn len(&self) -> usize {
        self.elements.len()
    }

    /// Check if pattern is empty
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Match pattern at specific position in sequence
    pub fn matches_at(&self, seq: &Sequential, start_pos: usize) -> bool {
        if start_pos + self.len() > seq.items.len() {
            return false;
        }

        for (i, pattern_elem) in self.elements.iter().enumerate() {
            if !pattern_elem.matches(&seq.items[start_pos + i]) {
                return false;
            }
        }

        true
    }

    /// Find all matches of this pattern in a sequence
    pub fn find_all(&self, seq: &Sequential) -> Vec<usize> {
        let mut matches = Vec::new();

        if seq.items.len() < self.len() {
            return matches;
        }

        for start_pos in 0..=(seq.items.len() - self.len()) {
            if self.matches_at(seq, start_pos) {
                matches.push(start_pos);
            }
        }

        matches
    }

    /// Find first match of this pattern in a sequence
    pub fn find_first(&self, seq: &Sequential) -> Option<usize> {
        if seq.items.len() < self.len() {
            return None;
        }

        (0..=(seq.items.len() - self.len())).find(|&start_pos| self.matches_at(seq, start_pos))
    }
}

/// A match result with position and matched slice
#[derive(Debug, Clone)]
pub struct Match {
    /// Start position in sequence
    pub position: usize,
    /// Length of match
    pub length: usize,
}

impl Match {
    pub fn new(position: usize, length: usize) -> Self {
        Match { position, length }
    }

    /// Get end position (exclusive)
    pub fn end(&self) -> usize {
        self.position + self.length
    }
}

/// Pattern matcher with multiple patterns
pub struct PatternMatcher {
    patterns: Vec<Pattern>,
}

impl PatternMatcher {
    /// Create a new pattern matcher
    pub fn new() -> Self {
        PatternMatcher { patterns: Vec::new() }
    }

    /// Add a pattern
    pub fn add_pattern(&mut self, pattern: Pattern) {
        self.patterns.push(pattern);
    }

    /// Find first matching pattern in sequence
    pub fn find_first_match(&self, seq: &Sequential) -> Option<(usize, &Pattern, Match)> {
        for (pattern_idx, pattern) in self.patterns.iter().enumerate() {
            if let Some(position) = pattern.find_first(seq) {
                return Some((pattern_idx, pattern, Match::new(position, pattern.len())));
            }
        }
        None
    }

    /// Find all matches of all patterns in sequence
    pub fn find_all_matches(&self, seq: &Sequential) -> Vec<(usize, &Pattern, Match)> {
        let mut all_matches = Vec::new();

        for (pattern_idx, pattern) in self.patterns.iter().enumerate() {
            for position in pattern.find_all(seq) {
                all_matches.push((pattern_idx, pattern, Match::new(position, pattern.len())));
            }
        }

        // Sort by position
        all_matches.sort_by_key(|(_, _, m)| m.position);

        all_matches
    }
}

impl Default for PatternMatcher {
    fn default() -> Self {
        Self::new()
    }
}

/// Helper macro to create patterns more concisely
#[macro_export]
macro_rules! pattern {
    // Exact matches: mark@c21
    ($($gen:ident @ c $class:literal),+ => $desc:expr) => {
        $crate::pattern::Pattern::new(
            vec![$($crate::pattern::PatternElement::exact(
                $crate::types::Generator::$gen,
                $class
            )),+],
            $desc
        )
    };

    // Any class matches: mark@*
    ($($gen:ident @ *),+ => $desc:expr) => {
        $crate::pattern::Pattern::new(
            vec![$($crate::pattern::PatternElement::any_class(
                $crate::types::Generator::$gen
            )),+],
            $desc
        )
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::ClassSigil;

    fn make_op(gen: Generator, class: u8) -> Term {
        Term::Operation {
            generator: gen,
            target: crate::types::ClassTarget::Single(ClassSigil::new(class).unwrap()),
        }
    }

    #[test]
    fn test_pattern_element_exact_match() {
        let elem = PatternElement::exact(Generator::Mark, 21);
        let term = make_op(Generator::Mark, 21);
        assert!(elem.matches(&term));

        let term2 = make_op(Generator::Mark, 22);
        assert!(!elem.matches(&term2));

        let term3 = make_op(Generator::Copy, 21);
        assert!(!elem.matches(&term3));
    }

    #[test]
    fn test_pattern_element_any_class() {
        let elem = PatternElement::any_class(Generator::Mark);
        let term1 = make_op(Generator::Mark, 21);
        let term2 = make_op(Generator::Mark, 42);
        let term3 = make_op(Generator::Copy, 21);

        assert!(elem.matches(&term1));
        assert!(elem.matches(&term2));
        assert!(!elem.matches(&term3));
    }

    #[test]
    fn test_pattern_element_any() {
        let elem = PatternElement::any();
        let term1 = make_op(Generator::Mark, 21);
        let term2 = make_op(Generator::Copy, 42);

        assert!(elem.matches(&term1));
        assert!(elem.matches(&term2));
    }

    #[test]
    fn test_pattern_matches_at() {
        // Pattern: mark@c21, copy@c05
        let pattern = Pattern::new(
            vec![
                PatternElement::exact(Generator::Mark, 21),
                PatternElement::exact(Generator::Copy, 5),
            ],
            "test",
        );

        // Sequence: mark@c21, copy@c05, mark@c42
        let seq = Sequential::new(vec![
            make_op(Generator::Mark, 21),
            make_op(Generator::Copy, 5),
            make_op(Generator::Mark, 42),
        ]);

        assert!(pattern.matches_at(&seq, 0));
        assert!(!pattern.matches_at(&seq, 1));
    }

    #[test]
    fn test_pattern_find_first() {
        let pattern = Pattern::new(
            vec![
                PatternElement::exact(Generator::Copy, 5),
                PatternElement::exact(Generator::Mark, 21),
            ],
            "H gate",
        );

        // Sequence with pattern at position 1
        let seq = Sequential::new(vec![
            make_op(Generator::Mark, 0),
            make_op(Generator::Copy, 5), // Pattern starts here
            make_op(Generator::Mark, 21),
            make_op(Generator::Mark, 42),
        ]);

        assert_eq!(pattern.find_first(&seq), Some(1));
    }

    #[test]
    fn test_pattern_find_all() {
        let pattern = Pattern::new(vec![PatternElement::exact(Generator::Mark, 21)], "single mark");

        // Sequence with pattern at positions 0, 2, 4
        let seq = Sequential::new(vec![
            make_op(Generator::Mark, 21), // Match
            make_op(Generator::Copy, 5),
            make_op(Generator::Mark, 21), // Match
            make_op(Generator::Copy, 5),
            make_op(Generator::Mark, 21), // Match
        ]);

        assert_eq!(pattern.find_all(&seq), vec![0, 2, 4]);
    }

    #[test]
    fn test_pattern_matcher() {
        let mut matcher = PatternMatcher::new();

        // Add patterns
        matcher.add_pattern(Pattern::new(
            vec![
                PatternElement::exact(Generator::Copy, 5),
                PatternElement::exact(Generator::Mark, 21),
            ],
            "H gate",
        ));

        matcher.add_pattern(Pattern::new(vec![PatternElement::exact(Generator::Mark, 21)], "X gate"));

        // Sequence: Copy@c5, Mark@c21, Mark@c21
        // H pattern (Copy,Mark) matches at 0
        // X pattern (Mark) matches at 1 and 2
        let seq = Sequential::new(vec![
            make_op(Generator::Copy, 5),
            make_op(Generator::Mark, 21),
            make_op(Generator::Mark, 21),
        ]);

        let matches = matcher.find_all_matches(&seq);
        assert_eq!(matches.len(), 3); // H at 0, X at 1, X at 2

        // Verify first match is H gate at position 0
        assert_eq!(matches[0].0, 0); // Pattern index 0 (H gate)
        assert_eq!(matches[0].2.position, 0);
        assert_eq!(matches[0].2.length, 2);
    }

    #[test]
    fn test_pattern_no_match() {
        let pattern = Pattern::new(
            vec![
                PatternElement::exact(Generator::Copy, 5),
                PatternElement::exact(Generator::Mark, 21),
            ],
            "H gate",
        );

        let seq = Sequential::new(vec![make_op(Generator::Mark, 0), make_op(Generator::Mark, 42)]);

        assert_eq!(pattern.find_first(&seq), None);
        assert_eq!(pattern.find_all(&seq), Vec::<usize>::new());
    }

    #[test]
    fn test_pattern_overlapping() {
        // Pattern that could overlap: mark@c21, mark@c21
        let pattern = Pattern::new(
            vec![
                PatternElement::exact(Generator::Mark, 21),
                PatternElement::exact(Generator::Mark, 21),
            ],
            "double mark",
        );

        // Sequence: mark@c21, mark@c21, mark@c21
        let seq = Sequential::new(vec![
            make_op(Generator::Mark, 21),
            make_op(Generator::Mark, 21),
            make_op(Generator::Mark, 21),
        ]);

        // Should find matches at positions 0 and 1
        assert_eq!(pattern.find_all(&seq), vec![0, 1]);
    }
}
