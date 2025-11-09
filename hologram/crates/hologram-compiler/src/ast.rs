//! Abstract Syntax Tree (AST) for Sigil Expressions
//!
//! Represents the parsed structure of sigil expressions following the grammar:
//!
//! ```text
//! <phrase>     ::= [ <transform> "@" ] <par>
//! <par>        ::= <seq> { "||" <seq> }              // parallel ⊗
//! <seq>        ::= <term> { "." <term> }             // sequential ∘
//! <term>       ::= <op> | "(" <par> ")"
//! <op>         ::= <generator> "@" <sigil>
//! <sigil>      ::= "c" <0..95> ["^" ("+"|"-") <k>] ["~"] ["@" <λ:0..47>]
//! <transform>  ::= [ "R" ("+"|"-") <q> ] [ "T" ("+"|"-") <k> ] [ "~" ]
//! ```

use crate::types::{ClassTarget, Generator, Transform};
use std::fmt;

/// A complete phrase (top-level expression)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Phrase {
    /// Transformed parallel composition
    Transformed { transform: Transform, body: Box<Parallel> },
    /// Direct parallel composition
    Parallel(Parallel),
}

/// Parallel composition (⊗) - multiple sequential branches
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parallel {
    pub branches: Vec<Sequential>,
}

impl Parallel {
    pub fn new(branches: Vec<Sequential>) -> Self {
        Parallel { branches }
    }

    pub fn single(seq: Sequential) -> Self {
        Parallel { branches: vec![seq] }
    }
}

/// Sequential composition (∘) - ordered list of terms (right-to-left execution)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sequential {
    pub items: Vec<Term>,
}

impl Sequential {
    pub fn new(items: Vec<Term>) -> Self {
        Sequential { items }
    }

    pub fn single(term: Term) -> Self {
        Sequential { items: vec![term] }
    }
}

/// A term in the expression (operation or grouped parallel)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// Generator applied to class target (single class or range)
    Operation { generator: Generator, target: ClassTarget },
    /// Grouped parallel composition
    Group(Box<Parallel>),
}

impl Phrase {
    /// Get the parallel body, whether transformed or not
    pub fn body(&self) -> &Parallel {
        match self {
            Phrase::Transformed { body, .. } => body,
            Phrase::Parallel(par) => par,
        }
    }

    /// Get the transform if present
    pub fn transform(&self) -> Option<&Transform> {
        match self {
            Phrase::Transformed { transform, .. } => Some(transform),
            Phrase::Parallel(_) => None,
        }
    }
}

// ============================================================================
// Display Implementations for AST Serialization
// ============================================================================

impl fmt::Display for Phrase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Phrase::Transformed { transform, body } => {
                write!(f, "{} @ {}", transform, body)
            }
            Phrase::Parallel(par) => write!(f, "{}", par),
        }
    }
}

impl fmt::Display for Parallel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, branch) in self.branches.iter().enumerate() {
            if i > 0 {
                write!(f, " || ")?;
            }
            write!(f, "{}", branch)?;
        }
        Ok(())
    }
}

impl fmt::Display for Sequential {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, item) in self.items.iter().enumerate() {
            if i > 0 {
                write!(f, " . ")?;
            }
            write!(f, "{}", item)?;
        }
        Ok(())
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Operation { generator, target } => {
                write!(f, "{} @ {}", generator, target)
            }
            Term::Group(par) => write!(f, "({})", par),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ast_construction() {
        // Build: copy@c05 . mark@c21
        let target1 = ClassTarget::single(5).unwrap();
        let target2 = ClassTarget::single(21).unwrap();

        let term1 = Term::Operation {
            generator: Generator::Copy,
            target: target1,
        };

        let term2 = Term::Operation {
            generator: Generator::Mark,
            target: target2,
        };

        let seq = Sequential::new(vec![term1, term2]);
        let par = Parallel::single(seq);
        let phrase = Phrase::Parallel(par);

        assert_eq!(phrase.body().branches.len(), 1);
        assert_eq!(phrase.body().branches[0].items.len(), 2);
    }

    #[test]
    fn test_transformed_phrase() {
        let target = ClassTarget::single(0).unwrap();
        let term = Term::Operation {
            generator: Generator::Mark,
            target,
        };

        let seq = Sequential::single(term);
        let par = Parallel::single(seq);

        let transform = Transform::new().with_rotate(1);
        let phrase = Phrase::Transformed {
            transform,
            body: Box::new(par),
        };

        assert!(phrase.transform().is_some());
        assert_eq!(phrase.transform().unwrap().r, Some(1));
    }

    #[test]
    fn test_parallel_composition() {
        // Build: mark@c01 || mark@c02
        let target1 = ClassTarget::single(1).unwrap();
        let target2 = ClassTarget::single(2).unwrap();

        let term1 = Term::Operation {
            generator: Generator::Mark,
            target: target1,
        };
        let term2 = Term::Operation {
            generator: Generator::Mark,
            target: target2,
        };

        let seq1 = Sequential::single(term1);
        let seq2 = Sequential::single(term2);

        let par = Parallel::new(vec![seq1, seq2]);

        assert_eq!(par.branches.len(), 2);
    }

    #[test]
    fn test_range_operation() {
        // Build: merge@c[0..9]
        let target = ClassTarget::range(0, 9).unwrap();
        let term = Term::Operation {
            generator: Generator::Merge,
            target,
        };

        let seq = Sequential::single(term);
        let par = Parallel::single(seq);
        let phrase = Phrase::Parallel(par);

        assert_eq!(phrase.body().branches.len(), 1);
        assert_eq!(phrase.body().branches[0].items.len(), 1);

        match &phrase.body().branches[0].items[0] {
            Term::Operation { generator, target } => {
                assert_eq!(*generator, Generator::Merge);
                assert!(target.is_range());

                if let ClassTarget::Range(range) = target {
                    assert_eq!(range.start_class(), 0);
                    assert_eq!(range.end_class(), 9);
                    assert_eq!(range.num_classes(), 10);
                }
            }
            _ => panic!("Expected operation"),
        }
    }
}
