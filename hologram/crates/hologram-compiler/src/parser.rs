//! Parser for Sigil Expressions
//!
//! Implements a recursive descent parser for the sigil expression grammar.
//!
//! ## Grammar
//!
//! ```text
//! <phrase>     ::= [ <transform> "@" ] <par>
//! <par>        ::= <seq> { "||" <seq> }              // parallel ⊗
//! <seq>        ::= <term> { "." <term> }             // sequential ∘
//! <term>       ::= <op> | "(" <par> ")"
//! <op>         ::= <generator> "@" <target>
//! <target>     ::= <single-class> | <range>
//!
//! <single-class> ::= "c" <0..95> ["^" ("+"|"-") <k>] ["~"] ["@" <λ:0..47>]
//! <range>        ::= "c" "[" <start:0..95> ".." <end:0..95> "]" ["^" ("+"|"-") <k>] ["~"]
//!
//! <transform>  ::= [ "R" ("+"|"-") <q> ] [ "T" ("+"|"-") <k> ] [ "~" ]
//! <generator>  ::= "mark" | "copy" | "swap" | "merge" | "split" | "quote" | "evaluate"
//! ```
//!
//! ## Examples
//!
//! ### Single Class Operations
//!
//! ```
//! use hologram_compiler::parser::parse;
//!
//! // Simple operation: mark@c21
//! let phrase = parse("mark@c21").unwrap();
//!
//! // With transforms: mark@c42^+3~
//! let phrase = parse("mark@c42^+3~").unwrap();
//!
//! // With page specifier for explicit copy: copy@c05->c06@17
//! let phrase = parse("copy@c05->c06@17").unwrap();
//! ```
//!
//! ### Range Operations
//!
//! ```
//! use hologram_compiler::parser::parse;
//!
//! // Simple range: merge@c[0..9]
//! let phrase = parse("merge@c[0..9]").unwrap();
//!
//! // Range with transforms: merge@c[5..14]^+1~
//! let phrase = parse("merge@c[5..14]^+1~").unwrap();
//!
//! // Large vector: merge@c[0..32] (100K elements)
//! let phrase = parse("merge@c[0..32]").unwrap();
//! ```
//!
//! ### Composition
//!
//! ```
//! use hologram_compiler::parser::parse;
//!
//! // Sequential: mark@c0 . merge@c[5..9] . mark@c20
//! let phrase = parse("mark@c0 . merge@c[5..9] . mark@c20").unwrap();
//!
//! // Parallel: mark@c[0..4] || mark@c[5..9]
//! let phrase = parse("mark@c[0..4] || mark@c[5..9]").unwrap();
//!
//! // Mixed: (mark@c1 || mark@c2) . merge@c[10..15]
//! let phrase = parse("(mark@c1 || mark@c2) . merge@c[10..15]").unwrap();
//! ```
//!
//! ### Global Transform
//!
//! ```
//! use hologram_compiler::parser::parse;
//!
//! // Apply transform to entire phrase
//! let phrase = parse("R+1 T-2 ~@ mark@c[0..9]").unwrap();
//! ```
//!
//! ## Supported Generators on Ranges
//!
//! - `mark` - Mark all classes in range
//! - `merge` - Merge operation across vector
//! - `quote` - Quote all classes in range
//! - `evaluate` - Evaluate all classes in range
//!
//! **Not supported**: `copy`, `swap`, `split` (require explicit source/dest)
//!
//! ## Range Constraints
//!
//! - Start must be less than end: `c[5..5]` is invalid
//! - Both indices must be in [0, 95]: `c[0..96]` is invalid
//! - Range is inclusive: `c[0..9]` includes classes 0 through 9 (10 classes)

use crate::ast::{Parallel, Phrase, Sequential, Term};
use crate::lexer::Token;
use crate::types::{ClassRange, ClassSigil, ClassTarget, Generator, Transform};
use std::str::FromStr;

/// Parser state
pub struct Parser {
    tokens: Vec<Token>,
    position: usize,
}

/// Parse errors
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseError {
    UnexpectedToken {
        expected: String,
        found: String,
        position: usize,
    },
    UnexpectedEof {
        expected: String,
    },
    InvalidGenerator {
        name: String,
    },
    InvalidClassIndex {
        value: i32,
    },
    InvalidPage {
        value: i32,
    },
    InvalidRange {
        start: i32,
        end: i32,
        message: String,
    },
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::UnexpectedToken {
                expected,
                found,
                position,
            } => {
                write!(f, "Expected {} but found {} at position {}", expected, found, position)
            }
            ParseError::UnexpectedEof { expected } => {
                write!(f, "Unexpected end of input, expected {}", expected)
            }
            ParseError::InvalidGenerator { name } => {
                write!(f, "Invalid generator name: {}", name)
            }
            ParseError::InvalidClassIndex { value } => {
                write!(f, "Class index {} out of range [0..95]", value)
            }
            ParseError::InvalidPage { value } => {
                write!(f, "Page {} out of range [0..47]", value)
            }
            ParseError::InvalidRange { start, end, message } => {
                write!(f, "Invalid range [{}..{}]: {}", start, end, message)
            }
        }
    }
}

impl std::error::Error for ParseError {}

pub type ParseResult<T> = Result<T, ParseError>;

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Parser { tokens, position: 0 }
    }

    /// Peek at current token
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.position)
    }

    /// Consume and return current token
    fn consume(&mut self) -> Option<Token> {
        if self.position < self.tokens.len() {
            let token = self.tokens[self.position].clone();
            self.position += 1;
            Some(token)
        } else {
            None
        }
    }

    /// Expect a specific token
    fn expect(&mut self, expected: Token) -> ParseResult<()> {
        match self.consume() {
            Some(token) if token == expected => Ok(()),
            Some(token) => Err(ParseError::UnexpectedToken {
                expected: format!("{}", expected),
                found: format!("{}", token),
                position: self.position - 1,
            }),
            None => Err(ParseError::UnexpectedEof {
                expected: format!("{}", expected),
            }),
        }
    }

    /// Parse a complete phrase
    /// `<phrase> ::= [ <transform> "@" ] <par>`
    pub fn parse_phrase(&mut self) -> ParseResult<Phrase> {
        // Check for prefix transform
        if self.is_transform_start() {
            let transform = self.parse_prefix_transform()?;
            self.expect(Token::At)?;
            let par = self.parse_parallel()?;
            Ok(Phrase::Transformed {
                transform,
                body: Box::new(par),
            })
        } else {
            let par = self.parse_parallel()?;
            Ok(Phrase::Parallel(par))
        }
    }

    /// Check if current position starts a transform
    fn is_transform_start(&self) -> bool {
        matches!(
            self.peek(),
            Some(Token::RotateMarker) | Some(Token::TwistMarker) | Some(Token::Tilde)
        )
    }

    /// Parse prefix transform
    /// <transform> ::= [ "R" ("+"|"-") <q> ] [ "T" ("+"|"-") <k> ] [ "~" ]
    fn parse_prefix_transform(&mut self) -> ParseResult<Transform> {
        let mut transform = Transform::new();

        // Parse R
        if matches!(self.peek(), Some(Token::RotateMarker)) {
            self.consume();
            let sign = self.parse_sign()?;
            let value = self.parse_number()?;
            transform.r = Some(sign * value);
        }

        // Parse T
        if matches!(self.peek(), Some(Token::TwistMarker)) {
            self.consume();
            let sign = self.parse_sign()?;
            let value = self.parse_number()?;
            transform.t = Some(sign * value);
        }

        // Parse ~
        if matches!(self.peek(), Some(Token::Tilde)) {
            self.consume();
            transform.m = true;
        }

        Ok(transform)
    }

    /// Parse a sign (+ or -)
    fn parse_sign(&mut self) -> ParseResult<i32> {
        match self.peek() {
            Some(Token::Plus) => {
                self.consume();
                Ok(1)
            }
            Some(Token::Minus) => {
                self.consume();
                Ok(-1)
            }
            _ => Ok(1), // Default to positive if no sign
        }
    }

    /// Parse a number
    fn parse_number(&mut self) -> ParseResult<i32> {
        match self.consume() {
            Some(Token::Number(n)) => Ok(n),
            Some(token) => Err(ParseError::UnexpectedToken {
                expected: "number".to_string(),
                found: format!("{}", token),
                position: self.position - 1,
            }),
            None => Err(ParseError::UnexpectedEof {
                expected: "number".to_string(),
            }),
        }
    }

    /// Parse parallel composition
    /// <par> ::= <seq> { "||" <seq> }
    fn parse_parallel(&mut self) -> ParseResult<Parallel> {
        let mut branches = vec![self.parse_sequential()?];

        while matches!(self.peek(), Some(Token::ParallelOp)) {
            self.consume();
            branches.push(self.parse_sequential()?);
        }

        Ok(Parallel::new(branches))
    }

    /// Parse sequential composition
    /// <seq> ::= <term> { "." <term> }
    fn parse_sequential(&mut self) -> ParseResult<Sequential> {
        let mut items = vec![self.parse_term()?];

        while matches!(self.peek(), Some(Token::Dot)) {
            self.consume();
            items.push(self.parse_term()?);
        }

        Ok(Sequential::new(items))
    }

    /// Parse a term
    /// <term> ::= <op> | "(" <par> ")"
    fn parse_term(&mut self) -> ParseResult<Term> {
        match self.peek() {
            Some(Token::LParen) => {
                self.consume();
                let par = self.parse_parallel()?;
                self.expect(Token::RParen)?;
                Ok(Term::Group(Box::new(par)))
            }
            Some(Token::Generator(_)) => {
                let (generator, target) = self.parse_operation()?;
                Ok(Term::Operation { generator, target })
            }
            Some(token) => Err(ParseError::UnexpectedToken {
                expected: "generator or '('".to_string(),
                found: format!("{}", token),
                position: self.position,
            }),
            None => Err(ParseError::UnexpectedEof {
                expected: "generator or '('".to_string(),
            }),
        }
    }

    /// Parse an operation
    /// <op> ::= <generator> "@" <class-target>
    fn parse_operation(&mut self) -> ParseResult<(Generator, ClassTarget)> {
        let generator = self.parse_generator()?;
        self.expect(Token::At)?;

        // Peek ahead to determine syntax type
        // Range syntax: c[...]
        // Single/multi-class syntax: c<number>...
        let is_range = if matches!(self.peek(), Some(Token::ClassMarker)) {
            // Save position to check what comes after 'c'
            let saved_pos = self.position;
            self.consume(); // consume 'c'
            let next = self.peek().cloned(); // Clone the token to avoid borrow issues
                                             // Restore position
            self.position = saved_pos;
            matches!(next, Some(Token::LBracket))
        } else {
            false
        };

        // Parse target based on generator type and syntax
        let target = if is_range {
            // Range syntax: merge@c[0..9]
            self.parse_class_target()?
        } else {
            match generator {
                Generator::Copy => self.parse_copy_target()?,
                Generator::Swap => self.parse_swap_target()?,
                Generator::Merge => self.parse_merge_or_split_target()?,
                Generator::Split => self.parse_merge_or_split_target()?,
                _ => self.parse_class_target()?, // Single for mark, quote, evaluate
            }
        };

        Ok((generator, target))
    }

    /// Parse a generator name
    fn parse_generator(&mut self) -> ParseResult<Generator> {
        match self.consume() {
            Some(Token::Generator(name)) => {
                Generator::from_str(&name).map_err(|_| ParseError::InvalidGenerator { name })
            }
            Some(token) => Err(ParseError::UnexpectedToken {
                expected: "generator".to_string(),
                found: format!("{}", token),
                position: self.position - 1,
            }),
            None => Err(ParseError::UnexpectedEof {
                expected: "generator".to_string(),
            }),
        }
    }

    /// Parse a class target (single class or range)
    /// <class-target> ::= "c" ( <class-index> | "[" <range> "]" ) <transforms>
    fn parse_class_target(&mut self) -> ParseResult<ClassTarget> {
        // Expect 'c'
        self.expect(Token::ClassMarker)?;

        // Check if it's a range or single class
        if matches!(self.peek(), Some(Token::LBracket)) {
            self.parse_class_range()
        } else {
            self.parse_single_class()
        }
    }

    /// Parse a single class sigil
    /// <single> ::= <0..95> ["^" ("+"|"-") <k>] ["~"] ["@" <λ:0..47>]
    fn parse_single_class(&mut self) -> ParseResult<ClassTarget> {
        // Parse class index
        let class_index = self.parse_number()?;
        if !(0..=95).contains(&class_index) {
            return Err(ParseError::InvalidClassIndex { value: class_index });
        }

        let mut sigil =
            ClassSigil::new(class_index as u8).map_err(|_| ParseError::InvalidClassIndex { value: class_index })?;

        // Parse optional postfix transform: ^(+|-)k
        if matches!(self.peek(), Some(Token::Caret)) {
            self.consume();
            let sign = self.parse_sign()?;
            let value = self.parse_number()?;
            sigil = sigil.with_twist(sign * value);
        }

        // Parse optional mirror: ~
        if matches!(self.peek(), Some(Token::Tilde)) {
            self.consume();
            sigil = sigil.with_mirror();
        }

        // Parse optional page: @λ
        if matches!(self.peek(), Some(Token::At)) {
            self.consume();
            let page = self.parse_number()?;
            if !(0..=47).contains(&page) {
                return Err(ParseError::InvalidPage { value: page });
            }
            sigil = sigil
                .with_page(page as u8)
                .map_err(|_| ParseError::InvalidPage { value: page })?;
        }

        Ok(ClassTarget::Single(sigil))
    }

    /// Parse a class range
    /// <range> ::= "[" <start:0..95> ".." <end:0..95> "]" <transforms>
    fn parse_class_range(&mut self) -> ParseResult<ClassTarget> {
        // Expect '['
        self.expect(Token::LBracket)?;

        // Parse start index
        let start = self.parse_number()?;
        if !(0..=95).contains(&start) {
            return Err(ParseError::InvalidClassIndex { value: start });
        }

        // Expect '..'
        self.expect(Token::DotDot)?;

        // Parse end index
        let end = self.parse_number()?;
        if !(0..=95).contains(&end) {
            return Err(ParseError::InvalidClassIndex { value: end });
        }

        // Expect ']'
        self.expect(Token::RBracket)?;

        // Validate range
        if start >= end {
            return Err(ParseError::InvalidRange {
                start,
                end,
                message: format!("Start {} must be less than end {}", start, end),
            });
        }

        let mut range = ClassRange::new(start as u8, end as u8).map_err(|msg| ParseError::InvalidRange {
            start,
            end,
            message: msg,
        })?;

        // Parse optional postfix transform: ^(+|-)k
        if matches!(self.peek(), Some(Token::Caret)) {
            self.consume();
            let sign = self.parse_sign()?;
            let value = self.parse_number()?;
            range = range.with_twist(sign * value);
        }

        // Parse optional mirror: ~
        if matches!(self.peek(), Some(Token::Tilde)) {
            self.consume();
            range = range.with_mirror();
        }

        Ok(ClassTarget::Range(range))
    }

    /// Parse copy target: c<src>->c<dst>
    fn parse_copy_target(&mut self) -> ParseResult<ClassTarget> {
        // Expect 'c' and parse source class
        self.expect(Token::ClassMarker)?;
        let src = self.parse_single_class_sigil()?;

        // Expect '->'
        self.expect(Token::Arrow)?;

        // Expect 'c' and parse destination class
        self.expect(Token::ClassMarker)?;
        let dst = self.parse_single_class_sigil()?;

        Ok(ClassTarget::CopyPair { src, dst })
    }

    /// Parse swap target: c<a><->c<b>
    fn parse_swap_target(&mut self) -> ParseResult<ClassTarget> {
        // Expect 'c' and parse first class
        self.expect(Token::ClassMarker)?;
        let a = self.parse_single_class_sigil()?;

        // Expect '<->'
        self.expect(Token::BiArrow)?;

        // Expect 'c' and parse second class
        self.expect(Token::ClassMarker)?;
        let b = self.parse_single_class_sigil()?;

        Ok(ClassTarget::SwapPair { a, b })
    }

    /// Parse merge/split target: c<primary>[c<context>,c<secondary>]
    fn parse_merge_or_split_target(&mut self) -> ParseResult<ClassTarget> {
        // Expect 'c' and parse primary class
        self.expect(Token::ClassMarker)?;
        let primary = self.parse_single_class_sigil()?;

        // Expect '['
        self.expect(Token::LBracket)?;

        // Expect 'c' and parse context class
        self.expect(Token::ClassMarker)?;
        let context = self.parse_single_class_sigil()?;

        // Expect ','
        self.expect(Token::Comma)?;

        // Expect 'c' and parse secondary class
        self.expect(Token::ClassMarker)?;
        let secondary = self.parse_single_class_sigil()?;

        // Expect ']'
        self.expect(Token::RBracket)?;

        Ok(ClassTarget::TripleClass {
            primary,
            context,
            secondary,
        })
    }

    /// Parse a single class sigil without ClassTarget wrapper
    /// Used by copy, swap, merge, split parsers
    fn parse_single_class_sigil(&mut self) -> ParseResult<ClassSigil> {
        // Parse class index
        let class_index = self.parse_number()?;
        if !(0..=95).contains(&class_index) {
            return Err(ParseError::InvalidClassIndex { value: class_index });
        }

        let mut sigil =
            ClassSigil::new(class_index as u8).map_err(|_| ParseError::InvalidClassIndex { value: class_index })?;

        // Parse optional postfix transform: ^(+|-)k
        if matches!(self.peek(), Some(Token::Caret)) {
            self.consume();
            let sign = self.parse_sign()?;
            let value = self.parse_number()?;
            sigil = sigil.with_twist(sign * value);
        }

        // Parse optional mirror: ~
        if matches!(self.peek(), Some(Token::Tilde)) {
            self.consume();
            sigil = sigil.with_mirror();
        }

        // Parse optional page: @λ
        if matches!(self.peek(), Some(Token::At)) {
            self.consume();
            let page = self.parse_number()?;
            if !(0..=47).contains(&page) {
                return Err(ParseError::InvalidPage { value: page });
            }
            sigil = sigil
                .with_page(page as u8)
                .map_err(|_| ParseError::InvalidPage { value: page })?;
        }

        Ok(sigil)
    }
}

/// Convenience function to parse a string into a phrase
pub fn parse(input: &str) -> ParseResult<Phrase> {
    let tokens = crate::lexer::tokenize(input);
    let mut parser = Parser::new(tokens);
    parser.parse_phrase()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_operation() {
        let phrase = parse("mark@c21").unwrap();
        let body = phrase.body();
        assert_eq!(body.branches.len(), 1);
        assert_eq!(body.branches[0].items.len(), 1);

        match &body.branches[0].items[0] {
            Term::Operation { generator, target } => {
                assert_eq!(*generator, Generator::Mark);
                assert!(target.is_single());
                if let ClassTarget::Single(sigil) = target {
                    assert_eq!(sigil.class_index, 21);
                }
            }
            _ => panic!("Expected operation"),
        }
    }

    #[test]
    fn test_parse_sequential() {
        let phrase = parse("copy@c05->c06 . mark@c21").unwrap();
        let body = phrase.body();
        assert_eq!(body.branches.len(), 1);
        assert_eq!(body.branches[0].items.len(), 2);
    }

    #[test]
    fn test_parse_parallel() {
        let phrase = parse("mark@c01 || mark@c02").unwrap();
        let body = phrase.body();
        assert_eq!(body.branches.len(), 2);
    }

    #[test]
    fn test_parse_prefix_transform() {
        let phrase = parse("R+1@ mark@c00").unwrap();
        assert!(phrase.transform().is_some());
        assert_eq!(phrase.transform().unwrap().r, Some(1));
    }

    #[test]
    fn test_parse_postfix_transform() {
        let phrase = parse("mark@c42^+3~").unwrap();
        let body = phrase.body();

        match &body.branches[0].items[0] {
            Term::Operation { target, .. } => {
                assert!(target.is_single());
                if let ClassTarget::Single(sigil) = target {
                    assert_eq!(sigil.class_index, 42);
                    assert_eq!(sigil.twist, Some(3));
                    assert!(sigil.mirror);
                }
            }
            _ => panic!("Expected operation"),
        }
    }

    #[test]
    fn test_parse_with_page() {
        let phrase = parse("mark@c00@17").unwrap();
        let body = phrase.body();

        match &body.branches[0].items[0] {
            Term::Operation { target, .. } => {
                assert!(target.is_single());
                if let ClassTarget::Single(sigil) = target {
                    assert_eq!(sigil.class_index, 0);
                    assert_eq!(sigil.page, Some(17));
                }
            }
            _ => panic!("Expected operation"),
        }
    }

    #[test]
    fn test_parse_grouped() {
        let phrase = parse("(mark@c01 || mark@c02) . mark@c03").unwrap();
        let body = phrase.body();
        assert_eq!(body.branches.len(), 1);
        assert_eq!(body.branches[0].items.len(), 2);

        match &body.branches[0].items[0] {
            Term::Group(par) => {
                assert_eq!(par.branches.len(), 2);
            }
            _ => panic!("Expected group"),
        }
    }

    #[test]
    fn test_parse_complex_transform() {
        let phrase = parse("R+2 T-3 ~@ mark@c00").unwrap();
        let transform = phrase.transform().unwrap();
        assert_eq!(transform.r, Some(2));
        assert_eq!(transform.t, Some(-3));
        assert!(transform.m);
    }

    #[test]
    fn test_invalid_class_index() {
        assert!(parse("mark@c96").is_err());
        assert!(parse("mark@c-1").is_err());
    }

    #[test]
    fn test_invalid_page() {
        assert!(parse("mark@c00@48").is_err());
        assert!(parse("mark@c00@-1").is_err());
    }

    #[test]
    fn test_all_generators() {
        // Test each generator with appropriate syntax
        assert!(parse("mark@c00").is_ok());

        let copy_result = parse("copy@c00->c01");
        if let Err(e) = &copy_result {
            eprintln!("Copy parse failed: {:?}", e);
        }
        assert!(copy_result.is_ok());

        assert!(parse("swap@c00<->c01").is_ok());
        assert!(parse("merge@c00[c01,c02]").is_ok());
        assert!(parse("split@c00[c01,c02]").is_ok());
        assert!(parse("quote@c00").is_ok());
        assert!(parse("evaluate@c00").is_ok());
    }

    // ========================================================================
    // Range Syntax Tests
    // ========================================================================

    #[test]
    fn test_parse_simple_range() {
        let phrase = parse("mark@c[0..9]").unwrap();
        let body = phrase.body();
        assert_eq!(body.branches.len(), 1);
        assert_eq!(body.branches[0].items.len(), 1);

        match &body.branches[0].items[0] {
            Term::Operation { generator, target } => {
                assert_eq!(*generator, Generator::Mark);
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

    #[test]
    fn test_parse_range_with_transforms() {
        let phrase = parse("merge@c[5..14]^+1~").unwrap();
        let body = phrase.body();

        match &body.branches[0].items[0] {
            Term::Operation { generator, target } => {
                assert_eq!(*generator, Generator::Merge);
                assert!(target.is_range());
                if let ClassTarget::Range(range) = target {
                    assert_eq!(range.start_class(), 5);
                    assert_eq!(range.end_class(), 14);
                    assert_eq!(range.num_classes(), 10);
                    assert_eq!(range.twist, Some(1));
                    assert!(range.mirror);
                }
            }
            _ => panic!("Expected operation"),
        }
    }

    #[test]
    fn test_parse_range_boundaries() {
        // Maximum range
        let phrase = parse("copy@c[0..94]").unwrap();
        let body = phrase.body();

        match &body.branches[0].items[0] {
            Term::Operation { target, .. } => {
                if let ClassTarget::Range(range) = target {
                    assert_eq!(range.start_class(), 0);
                    assert_eq!(range.end_class(), 94);
                    assert_eq!(range.num_classes(), 95);
                }
            }
            _ => panic!("Expected operation"),
        }

        // Minimum range (2 classes)
        let phrase = parse("mark@c[0..1]").unwrap();
        let body = phrase.body();

        match &body.branches[0].items[0] {
            Term::Operation { target, .. } => {
                if let ClassTarget::Range(range) = target {
                    assert_eq!(range.num_classes(), 2);
                }
            }
            _ => panic!("Expected operation"),
        }
    }

    #[test]
    fn test_parse_invalid_range() {
        // Start >= end
        assert!(parse("mark@c[5..5]").is_err());
        assert!(parse("mark@c[10..5]").is_err());

        // Out of bounds
        assert!(parse("mark@c[0..96]").is_err());
        assert!(parse("mark@c[96..100]").is_err());
    }

    #[test]
    fn test_parse_mixed_single_and_range() {
        let phrase = parse("mark@c5 . merge@c[10..19]").unwrap();
        let body = phrase.body();
        assert_eq!(body.branches.len(), 1);
        assert_eq!(body.branches[0].items.len(), 2);

        // First operation: single class
        match &body.branches[0].items[0] {
            Term::Operation { generator, target } => {
                assert_eq!(*generator, Generator::Mark);
                assert!(target.is_single());
            }
            _ => panic!("Expected operation"),
        }

        // Second operation: range
        match &body.branches[0].items[1] {
            Term::Operation { generator, target } => {
                assert_eq!(*generator, Generator::Merge);
                assert!(target.is_range());
            }
            _ => panic!("Expected operation"),
        }
    }

    #[test]
    fn test_parse_range_parallel() {
        let phrase = parse("mark@c[0..4] || merge@c[5..9]").unwrap();
        let body = phrase.body();
        assert_eq!(body.branches.len(), 2);

        // First branch: mark@c[0..4]
        match &body.branches[0].items[0] {
            Term::Operation { generator, target } => {
                assert_eq!(*generator, Generator::Mark);
                assert!(target.is_range());
            }
            _ => panic!("Expected operation"),
        }

        // Second branch: merge@c[5..9]
        match &body.branches[1].items[0] {
            Term::Operation { generator, target } => {
                assert_eq!(*generator, Generator::Merge);
                assert!(target.is_range());
            }
            _ => panic!("Expected operation"),
        }
    }
}
