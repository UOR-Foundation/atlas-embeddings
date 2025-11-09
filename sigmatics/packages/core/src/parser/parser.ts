/**
 * Atlas Parser
 * Parses tokenized sigil expressions into AST
 * Grammar (EBNF):
 *   <phrase>     ::= [ <transform> "@" ] <par>
 *   <par>        ::= <seq> { "||" <seq> }
 *   <seq>        ::= <term> { "." <term> }
 *   <term>       ::= <op> | "(" <par> ")"
 *   <op>         ::= <generator> "@" <sigil>
 *   <sigil>      ::= "c" <int:0..95> ["^" [("R"|"D"|"T")] ("+"|"-") <int>] ["~"] ["@" <λ:int 0..47>]
 *   <transform>  ::= [ "R" ("+"|"-") <int> ] [ "D" ("+"|"-") <int> ] [ "T" ("+"|"-") <int> ] [ "~" ]
 */

import { tokenize, type Token, type TokenType } from '../lexer';
import type {
  ClassSigil,
  Operation,
  Sequential,
  Parallel,
  Transform,
  Term,
  Phrase,
  GeneratorName,
} from '../types';

export class Parser {
  private tokens: Token[];
  private position = 0;

  constructor(tokens: Token[]) {
    this.tokens = tokens;
  }

  /**
   * Parse a complete phrase, ensuring all tokens are consumed.
   */
  parsePhrase(): Phrase {
    let phrase: Phrase;
    const currentType = this.current().type;

    // Use lookahead to decide whether to parse a transform prefix
    if (
      currentType === 'ROTATE' ||
      currentType === 'TRIALITY' ||
      currentType === 'TWIST' ||
      currentType === 'TILDE'
    ) {
      const transform = this.parseTransform();
      this.expect('AT');
      const body = this.parseParallel();
      phrase = {
        kind: 'Xform',
        transform,
        body,
      };
    } else {
      phrase = this.parseParallel();
    }

    this.expect('EOF'); // Ensure all tokens are consumed
    return phrase;
  }

  /**
   * Parse parallel composition: seq || seq || ...
   */
  private parseParallel(): Parallel {
    const branches: Sequential[] = [this.parseSequential()];

    while (this.current().type === 'PARALLEL') {
      this.advance(); // consume ||
      branches.push(this.parseSequential());
    }

    return {
      kind: 'Par',
      branches,
    };
  }

  /**
   * Parse sequential composition: term . term . ...
   */
  private parseSequential(): Sequential {
    const items: Term[] = [this.parseTerm()];

    while (this.current().type === 'DOT') {
      this.advance(); // consume .
      items.push(this.parseTerm());
    }

    return {
      kind: 'Seq',
      items,
    };
  }

  /**
   * Parse a term: op or grouped parallel
   */
  private parseTerm(): Term {
    const currentType = this.current().type;

    // Allow transform prefixes within sequences or groups
    if (
      currentType === 'ROTATE' ||
      currentType === 'TRIALITY' ||
      currentType === 'TWIST' ||
      currentType === 'TILDE'
    ) {
      const transform = this.parseTransform();
      this.expect('AT');
      const body = this.parseParallel();
      return {
        kind: 'Xform',
        transform,
        body,
      };
    }

    // Check for grouped expression
    if (currentType === 'LPAREN') {
      this.advance(); // consume (
      const body = this.parseParallel();
      this.expect('RPAREN');
      return {
        kind: 'Group',
        body,
      };
    }

    // Must be an operation
    return this.parseOperation();
  }

  /**
   * Parse an operation: generator @ sigil
   */
  private parseOperation(): Operation {
    const genToken = this.expect('GENERATOR');
    const generator = genToken.value as GeneratorName;

    this.expect('AT');

    const sigil = this.parseSigil();

    return {
      kind: 'Op',
      generator,
      sigil,
    };
  }

  /**
   * Parse a sigil: c<N> [^±k] [~] [@λ]
   */
  private parseSigil(): ClassSigil {
    const classToken = this.expect('CLASS');
    const classStr = classToken.value.substring(1); // remove 'c'
    const classIndex = parseInt(classStr, 10);

    if (classIndex < 0 || classIndex > 95) {
      throw new Error(
        `Class index ${classIndex} out of range [0..95] at position ${classToken.position}`,
      );
    }

    const sigil: ClassSigil = {
      kind: 'Sigil',
      classIndex,
    };

    // Check for postfix transforms ^[R|D|T]±k
    if (this.current().type === 'CARET') {
      this.advance(); // consume ^

      // Check if there's a transform letter (R, D, or T)
      const currentType = this.current().type;
      if (currentType === 'ROTATE') {
        this.advance(); // consume R
        const sign = this.parseSign();
        const k = parseInt(this.expect('NUMBER').value, 10);
        sigil.rotate = sign * k;
      } else if (currentType === 'TRIALITY') {
        this.advance(); // consume D
        const sign = this.parseSign();
        const k = parseInt(this.expect('NUMBER').value, 10);
        sigil.triality = sign * k;
      } else if (currentType === 'TWIST') {
        this.advance(); // consume T
        const sign = this.parseSign();
        const k = parseInt(this.expect('NUMBER').value, 10);
        sigil.twist = sign * k;
      } else {
        // Backward compatibility: ^±k defaults to twist
        const sign = this.parseSign();
        const k = parseInt(this.expect('NUMBER').value, 10);
        sigil.twist = sign * k;
      }
    }

    // Check for mirror ~
    if (this.current().type === 'TILDE') {
      this.advance();
      sigil.mirror = true;
    }

    // Check for page @λ
    if (this.current().type === 'AT') {
      this.advance(); // consume @
      const pageToken = this.expect('NUMBER');
      const page = parseInt(pageToken.value, 10);

      if (page < 0 || page > 47) {
        throw new Error(
          `Page index ${page} out of range [0..47] at position ${pageToken.position}`,
        );
      }

      sigil.page = page;
    }

    return sigil;
  }

  /**
   * Parse a transform prefix: [R±q] [D±k] [T±k] [~]
   */
  private parseTransform(): Transform {
    const transform: Transform = {};
    let hasAny = false;

    // Check for R±q
    if (this.current().type === 'ROTATE') {
      hasAny = true;
      this.advance(); // consume R
      const sign = this.parseSign();
      const q = parseInt(this.expect('NUMBER').value, 10);
      transform.R = sign * q;
    }

    // Check for D±k
    if (this.current().type === 'TRIALITY') {
      hasAny = true;
      this.advance(); // consume D
      const sign = this.parseSign();
      const k = parseInt(this.expect('NUMBER').value, 10);
      transform.D = sign * k;
    }

    // Check for T±k
    if (this.current().type === 'TWIST') {
      hasAny = true;
      this.advance(); // consume T
      const sign = this.parseSign();
      const k = parseInt(this.expect('NUMBER').value, 10);
      transform.T = sign * k;
    }

    // Check for ~
    if (this.current().type === 'TILDE') {
      hasAny = true;
      this.advance();
      transform.M = true;
    }

    if (!hasAny) {
      // This should not be reachable due to the lookahead in parsePhrase
      throw new Error(
        `Expected a transform token (R, D, T, or ~) at position ${this.current().position}`,
      );
    }

    return transform;
  }

  /**
   * Parse sign (+ or -)
   */
  private parseSign(): number {
    const token = this.current();
    if (token.type === 'PLUS') {
      this.advance();
      return 1;
    } else if (token.type === 'MINUS') {
      this.advance();
      return -1;
    }
    throw new Error(`Expected + or - at position ${token.position}`);
  }

  /**
   * Get current token
   */
  private current(): Token {
    return this.tokens[this.position];
  }

  /**
   * Advance to next token
   */
  private advance(): Token {
    return this.tokens[this.position++];
  }

  /**
   * Expect a specific token type
   */
  private expect(type: TokenType): Token {
    const token = this.current();
    if (token.type !== type) {
      throw new Error(`Expected ${type} but got ${token.type} at position ${token.position}`);
    }
    this.advance();
    return token;
  }
}

/**
 * Convenience function to parse a string into AST
 */
export function parse(source: string): Phrase {
  const tokens = tokenize(source);
  const parser = new Parser(tokens);
  return parser.parsePhrase();
}
