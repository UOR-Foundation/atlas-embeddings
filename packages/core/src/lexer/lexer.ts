/**
 * Atlas Lexer
 * Tokenizes sigil expressions according to the surface grammar
 */

export type TokenType =
  | 'CLASS' // c42
  | 'GENERATOR' // mark, copy, swap, merge, split, quote, evaluate
  | 'DOT' // .
  | 'PARALLEL' // ||
  | 'LPAREN' // (
  | 'RPAREN' // )
  | 'AT' // @
  | 'CARET' // ^
  | 'TILDE' // ~
  | 'PLUS' // +
  | 'MINUS' // -
  | 'NUMBER' // integer literal
  | 'ROTATE' // R
  | 'TRIALITY' // D
  | 'TWIST' // T
  | 'EOF'
  | 'ERROR';

export interface Token {
  type: TokenType;
  value: string;
  position: number;
  length: number;
}

const GENERATORS = new Set(['mark', 'copy', 'swap', 'merge', 'split', 'quote', 'evaluate']);

export class Lexer {
  private source: string;
  private position = 0;
  private tokens: Token[] = [];

  constructor(source: string) {
    this.source = source;
  }

  /**
   * Tokenize the entire source
   */
  tokenize(): Token[] {
    this.tokens = [];
    this.position = 0;

    while (this.position < this.source.length) {
      this.skipWhitespaceAndComments();

      if (this.position >= this.source.length) break;

      const token = this.nextToken();
      if (token.type === 'ERROR') {
        throw new Error(`Lexer error at position ${token.position}: unexpected '${token.value}'`);
      }
      this.tokens.push(token);
    }

    // Add EOF token
    this.tokens.push({
      type: 'EOF',
      value: '',
      position: this.position,
      length: 0,
    });

    return this.tokens;
  }

  private nextToken(): Token {
    const start = this.position;
    const char = this.source[this.position];

    // Single character tokens
    switch (char) {
      case '.':
        this.position++;
        return this.makeToken('DOT', '.', start);
      case '(':
        this.position++;
        return this.makeToken('LPAREN', '(', start);
      case ')':
        this.position++;
        return this.makeToken('RPAREN', ')', start);
      case '@':
        this.position++;
        return this.makeToken('AT', '@', start);
      case '^':
        this.position++;
        return this.makeToken('CARET', '^', start);
      case '~':
        this.position++;
        return this.makeToken('TILDE', '~', start);
      case '+':
        this.position++;
        return this.makeToken('PLUS', '+', start);
      case '-':
        this.position++;
        return this.makeToken('MINUS', '-', start);
    }

    // Check for ||
    if (char === '|' && this.peek() === '|') {
      this.position += 2;
      return this.makeToken('PARALLEL', '||', start);
    }

    // Check for class sigil (c followed by number) first, as it's more specific
    if (char === 'c' && this.isDigit(this.peek())) {
      return this.readClassSigil(start);
    }

    // Check for identifiers (generators) or R/T prefixes
    if (this.isAlpha(char)) {
      return this.readIdentifier(start);
    }

    // Check for numbers
    if (this.isDigit(char)) {
      return this.readNumber(start);
    }

    // Unknown character
    this.position++;
    return this.makeToken('ERROR', char, start);
  }

  private readIdentifier(start: number): Token {
    let value = '';

    while (this.position < this.source.length && this.isAlphaNumeric(this.source[this.position])) {
      value += this.source[this.position];
      this.position++;
    }

    // Check for R, D, or T transform prefixes
    if (value === 'R') {
      return this.makeToken('ROTATE', value, start);
    }
    if (value === 'D') {
      return this.makeToken('TRIALITY', value, start);
    }
    if (value === 'T') {
      return this.makeToken('TWIST', value, start);
    }

    // Check if it's a generator
    if (GENERATORS.has(value)) {
      return this.makeToken('GENERATOR', value, start);
    }

    // Unknown identifier
    return this.makeToken('ERROR', value, start);
  }

  private readNumber(start: number): Token {
    let value = '';

    while (this.position < this.source.length && this.isDigit(this.source[this.position])) {
      value += this.source[this.position];
      this.position++;
    }

    return this.makeToken('NUMBER', value, start);
  }

  private readClassSigil(start: number): Token {
    let value = 'c';
    this.position++; // skip 'c'

    // Read the number
    while (this.position < this.source.length && this.isDigit(this.source[this.position])) {
      value += this.source[this.position];
      this.position++;
    }

    return this.makeToken('CLASS', value, start);
  }

  private skipWhitespaceAndComments(): void {
    while (this.position < this.source.length) {
      const char = this.source[this.position];

      // Skip whitespace
      if (this.isWhitespace(char)) {
        this.position++;
        continue;
      }

      // Skip comments (// to end of line)
      if (char === '/' && this.peek() === '/') {
        this.position += 2;
        while (this.position < this.source.length && this.source[this.position] !== '\n') {
          this.position++;
        }
        continue;
      }

      break;
    }
  }

  private peek(offset = 1): string {
    const pos = this.position + offset;
    return pos < this.source.length ? this.source[pos] : '';
  }

  private isWhitespace(char: string): boolean {
    return char === ' ' || char === '\t' || char === '\n' || char === '\r';
  }

  private isAlpha(char: string): boolean {
    return (char >= 'a' && char <= 'z') || (char >= 'A' && char <= 'Z');
  }

  private isDigit(char: string): boolean {
    return char >= '0' && char <= '9';
  }

  private isAlphaNumeric(char: string): boolean {
    return this.isAlpha(char) || this.isDigit(char);
  }

  private makeToken(type: TokenType, value: string, start: number): Token {
    return {
      type,
      value,
      position: start,
      length: this.position - start,
    };
  }
}

/**
 * Convenience function to tokenize a string
 */
export function tokenize(source: string): Token[] {
  const lexer = new Lexer(source);
  return lexer.tokenize();
}
