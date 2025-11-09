//! Lexer/Tokenizer for Sigil Expressions
//!
//! Converts input strings into a stream of tokens for parsing.
//!
//! ## Examples
//!
//! ### Single Class Operation
//!
//! ```
//! use hologram_compiler::lexer::tokenize;
//!
//! let tokens = tokenize("mark@c21");
//! // Produces: [Generator("mark"), At, ClassMarker, Number(21)]
//! ```
//!
//! ### Range Operation
//!
//! ```
//! use hologram_compiler::lexer::tokenize;
//!
//! let tokens = tokenize("merge@c[0..9]");
//! // Produces: [Generator("merge"), At, ClassMarker, LBracket,
//! //            Number(0), DotDot, Number(9), RBracket]
//! ```
//!
//! ### Range with Transforms
//!
//! ```
//! use hologram_compiler::lexer::tokenize;
//!
//! let tokens = tokenize("merge@c[5..14]^+1~");
//! // Produces: [Generator("merge"), At, ClassMarker, LBracket,
//! //            Number(5), DotDot, Number(14), RBracket,
//! //            Caret, Plus, Number(1), Tilde]
//! ```
//!
//! ### Composition with Ranges
//!
//! ```
//! use hologram_compiler::lexer::tokenize;
//!
//! let tokens = tokenize("mark@c0 . merge@c[5..9] . mark@c20");
//! // Sequential composition mixing single classes and ranges
//! ```

use std::fmt;

/// Token types in sigil expressions
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    // Generators
    Generator(String), // mark, copy, swap, merge, split, quote, evaluate

    // Operators
    At,         // @
    Dot,        // .
    DotDot,     // .. (range operator)
    ParallelOp, // ||
    Caret,      // ^
    Tilde,      // ~
    Plus,       // +
    Minus,      // -
    Arrow,      // -> (copy destination)
    BiArrow,    // <-> (swap pair)
    Comma,      // , (separator in multi-class specs)

    // Grouping
    LParen,   // (
    RParen,   // )
    LBracket, // [
    RBracket, // ]

    // Literals
    Number(i32), // Any number
    ClassMarker, // c (followed by number for class index)

    // Transform markers
    RotateMarker, // R
    TwistMarker,  // T
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Generator(name) => write!(f, "Generator({})", name),
            Token::At => write!(f, "@"),
            Token::Dot => write!(f, "."),
            Token::DotDot => write!(f, ".."),
            Token::ParallelOp => write!(f, "||"),
            Token::Caret => write!(f, "^"),
            Token::Tilde => write!(f, "~"),
            Token::Plus => write!(f, "+"),
            Token::Minus => write!(f, "-"),
            Token::Arrow => write!(f, "->"),
            Token::BiArrow => write!(f, "<->"),
            Token::Comma => write!(f, ","),
            Token::LParen => write!(f, "("),
            Token::RParen => write!(f, ")"),
            Token::LBracket => write!(f, "["),
            Token::RBracket => write!(f, "]"),
            Token::Number(n) => write!(f, "Number({})", n),
            Token::ClassMarker => write!(f, "c"),
            Token::RotateMarker => write!(f, "R"),
            Token::TwistMarker => write!(f, "T"),
        }
    }
}

/// Lexer state
pub struct Lexer<'a> {
    input: &'a str,
    position: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Lexer { input, position: 0 }
    }

    /// Peek at current character without consuming
    fn peek(&self) -> Option<char> {
        self.input[self.position..].chars().next()
    }

    /// Consume and return current character
    fn consume(&mut self) -> Option<char> {
        let ch = self.peek()?;
        self.position += ch.len_utf8();
        Some(ch)
    }

    /// Skip whitespace
    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.peek() {
            if ch.is_whitespace() {
                self.consume();
            } else {
                break;
            }
        }
    }

    /// Read an identifier (generator name or keyword)
    fn read_identifier(&mut self) -> String {
        let mut result = String::new();
        while let Some(ch) = self.peek() {
            if ch.is_alphabetic() || ch == '_' {
                result.push(ch);
                self.consume();
            } else {
                break;
            }
        }
        result
    }

    /// Read a number (positive only, sign handled as separate token)
    fn read_number(&mut self) -> i32 {
        let mut result = String::new();

        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() {
                result.push(ch);
                self.consume();
            } else {
                break;
            }
        }

        result.parse().unwrap_or(0)
    }

    /// Get next token
    pub fn next_token(&mut self) -> Option<Token> {
        self.skip_whitespace();

        let ch = self.peek()?;

        match ch {
            // Single character tokens
            '@' => {
                self.consume();
                Some(Token::At)
            }
            '.' => {
                self.consume();
                // Check for .. (range operator)
                if self.peek() == Some('.') {
                    self.consume();
                    Some(Token::DotDot)
                } else {
                    Some(Token::Dot)
                }
            }
            '^' => {
                self.consume();
                Some(Token::Caret)
            }
            '~' => {
                self.consume();
                Some(Token::Tilde)
            }
            '+' => {
                self.consume();
                Some(Token::Plus)
            }
            '-' => {
                self.consume();
                // Check for -> (arrow)
                if self.peek() == Some('>') {
                    self.consume();
                    Some(Token::Arrow)
                } else {
                    Some(Token::Minus)
                }
            }
            '(' => {
                self.consume();
                Some(Token::LParen)
            }
            ')' => {
                self.consume();
                Some(Token::RParen)
            }
            '[' => {
                self.consume();
                Some(Token::LBracket)
            }
            ']' => {
                self.consume();
                Some(Token::RBracket)
            }
            ',' => {
                self.consume();
                Some(Token::Comma)
            }
            '<' => {
                self.consume();
                // Check for <-> (bi-arrow)
                if self.peek() == Some('-') {
                    self.consume();
                    if self.peek() == Some('>') {
                        self.consume();
                        Some(Token::BiArrow)
                    } else {
                        // Invalid sequence <-, skip
                        self.next_token()
                    }
                } else {
                    // Single < not valid, skip
                    self.next_token()
                }
            }
            '|' => {
                // Check for ||
                self.consume();
                if self.peek() == Some('|') {
                    self.consume();
                    Some(Token::ParallelOp)
                } else {
                    // Single | not valid, but return it anyway
                    Some(Token::ParallelOp)
                }
            }

            // Numbers
            '0'..='9' => Some(Token::Number(self.read_number())),

            // Identifiers and keywords
            'a'..='z' | 'A'..='Z' => {
                let ident = self.read_identifier();
                match ident.as_str() {
                    "mark" | "copy" | "swap" | "merge" | "split" | "quote" | "evaluate" => {
                        Some(Token::Generator(ident))
                    }
                    "c" => Some(Token::ClassMarker),
                    "R" => Some(Token::RotateMarker),
                    "T" => Some(Token::TwistMarker),
                    _ => {
                        // Unknown identifier, treat as generator for now
                        Some(Token::Generator(ident))
                    }
                }
            }

            _ => {
                // Unknown character, skip it
                self.consume();
                self.next_token()
            }
        }
    }

    /// Tokenize entire input
    pub fn tokenize(&mut self) -> Vec<Token> {
        let mut tokens = Vec::new();
        while let Some(token) = self.next_token() {
            tokens.push(token);
        }
        tokens
    }
}

/// Convenience function to tokenize a string
pub fn tokenize(input: &str) -> Vec<Token> {
    let mut lexer = Lexer::new(input);
    lexer.tokenize()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_operation() {
        let tokens = tokenize("mark@c21");
        assert_eq!(
            tokens,
            vec![
                Token::Generator("mark".to_string()),
                Token::At,
                Token::ClassMarker,
                Token::Number(21),
            ]
        );
    }

    #[test]
    fn test_sequential_composition() {
        let tokens = tokenize("copy@c05 . mark@c21");
        assert_eq!(
            tokens,
            vec![
                Token::Generator("copy".to_string()),
                Token::At,
                Token::ClassMarker,
                Token::Number(5),
                Token::Dot,
                Token::Generator("mark".to_string()),
                Token::At,
                Token::ClassMarker,
                Token::Number(21),
            ]
        );
    }

    #[test]
    fn test_parallel_composition() {
        let tokens = tokenize("mark@c01 || mark@c02");
        assert_eq!(
            tokens,
            vec![
                Token::Generator("mark".to_string()),
                Token::At,
                Token::ClassMarker,
                Token::Number(1),
                Token::ParallelOp,
                Token::Generator("mark".to_string()),
                Token::At,
                Token::ClassMarker,
                Token::Number(2),
            ]
        );
    }

    #[test]
    fn test_transforms() {
        let tokens = tokenize("R+1 T-2 ~@ mark@c00");
        assert_eq!(
            tokens,
            vec![
                Token::RotateMarker,
                Token::Plus,
                Token::Number(1),
                Token::TwistMarker,
                Token::Minus,
                Token::Number(2),
                Token::Tilde,
                Token::At,
                Token::Generator("mark".to_string()),
                Token::At,
                Token::ClassMarker,
                Token::Number(0),
            ]
        );
    }

    #[test]
    fn test_postfix_transforms() {
        let tokens = tokenize("mark@c42^+3~@17");
        assert_eq!(
            tokens,
            vec![
                Token::Generator("mark".to_string()),
                Token::At,
                Token::ClassMarker,
                Token::Number(42),
                Token::Caret,
                Token::Plus,
                Token::Number(3),
                Token::Tilde,
                Token::At,
                Token::Number(17),
            ]
        );
    }

    #[test]
    fn test_grouping() {
        let tokens = tokenize("(mark@c01 || mark@c02)");
        assert_eq!(
            tokens,
            vec![
                Token::LParen,
                Token::Generator("mark".to_string()),
                Token::At,
                Token::ClassMarker,
                Token::Number(1),
                Token::ParallelOp,
                Token::Generator("mark".to_string()),
                Token::At,
                Token::ClassMarker,
                Token::Number(2),
                Token::RParen,
            ]
        );
    }

    #[test]
    fn test_all_generators() {
        for gen in ["mark", "copy", "swap", "merge", "split", "quote", "evaluate"] {
            let input = format!("{}@c00", gen);
            let tokens = tokenize(&input);
            assert_eq!(tokens[0], Token::Generator(gen.to_string()));
        }
    }

    #[test]
    fn test_whitespace_handling() {
        let tokens1 = tokenize("mark@c21.copy@c05");
        let tokens2 = tokenize("mark @ c21 . copy @ c05");
        assert_eq!(tokens1, tokens2);
    }

    #[test]
    fn test_bracket_tokens() {
        let tokens = tokenize("[]");
        assert_eq!(tokens, vec![Token::LBracket, Token::RBracket]);
    }

    #[test]
    fn test_range_operator() {
        let tokens = tokenize("..");
        assert_eq!(tokens, vec![Token::DotDot]);
    }

    #[test]
    fn test_range_syntax() {
        let tokens = tokenize("mark@c[0..9]");
        assert_eq!(
            tokens,
            vec![
                Token::Generator("mark".to_string()),
                Token::At,
                Token::ClassMarker,
                Token::LBracket,
                Token::Number(0),
                Token::DotDot,
                Token::Number(9),
                Token::RBracket,
            ]
        );
    }

    #[test]
    fn test_range_with_transforms() {
        let tokens = tokenize("merge@c[5..14]^+1~");
        assert_eq!(
            tokens,
            vec![
                Token::Generator("merge".to_string()),
                Token::At,
                Token::ClassMarker,
                Token::LBracket,
                Token::Number(5),
                Token::DotDot,
                Token::Number(14),
                Token::RBracket,
                Token::Caret,
                Token::Plus,
                Token::Number(1),
                Token::Tilde,
            ]
        );
    }

    #[test]
    fn test_mixed_dot_and_dotdot() {
        // Test that single . and .. are distinguished
        let tokens = tokenize("mark@c1 . merge@c[0..5]");
        assert_eq!(
            tokens,
            vec![
                Token::Generator("mark".to_string()),
                Token::At,
                Token::ClassMarker,
                Token::Number(1),
                Token::Dot, // Single dot (sequential composition)
                Token::Generator("merge".to_string()),
                Token::At,
                Token::ClassMarker,
                Token::LBracket,
                Token::Number(0),
                Token::DotDot, // Double dot (range)
                Token::Number(5),
                Token::RBracket,
            ]
        );
    }

    #[test]
    fn test_range_boundaries() {
        let tokens = tokenize("copy@c[0..94]");
        assert_eq!(
            tokens,
            vec![
                Token::Generator("copy".to_string()),
                Token::At,
                Token::ClassMarker,
                Token::LBracket,
                Token::Number(0),
                Token::DotDot,
                Token::Number(94),
                Token::RBracket,
            ]
        );
    }
}
