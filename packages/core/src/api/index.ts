/**
 * Atlas - Main API
 * User-facing programming interface
 */

import { tokenize } from '../lexer';
import { Parser } from '../parser';
import {
  evaluateLiteral,
  evaluateOperational,
  formatBytes,
  formatAddresses,
  formatWords,
} from '../evaluator';
import {
  byteToClassIndex,
  classIndexToCanonicalByte,
  getClassInfo,
  areEquivalent,
  getEquivalenceClass,
  formatClassInfo,
  computeBeltAddress,
  decomposeBeltAddress,
} from '../class-system';
import type {
  Phrase,
  LiteralResult,
  OperationalResult,
  ClassInfo,
  BeltAddress,
} from '../types';

// ============================================================================
// High-Level API
// ============================================================================

export class Atlas {
  /**
   * Parse a sigil expression into AST
   */
  static parse(source: string): Phrase {
    const tokens = tokenize(source);
    const parser = new Parser(tokens);
    return parser.parsePhrase();
  }

  /**
   * Evaluate to bytes (literal backend)
   */
  static evaluateBytes(source: string): LiteralResult {
    const ast = this.parse(source);
    return evaluateLiteral(ast);
  }

  /**
   * Evaluate to words (operational backend)
   */
  static evaluateWords(source: string): OperationalResult {
    const ast = this.parse(source);
    return evaluateOperational(ast);
  }

  /**
   * Complete evaluation - returns both backends
   */
  static evaluate(source: string): {
    ast: Phrase;
    literal: LiteralResult;
    operational: OperationalResult;
  } {
    const ast = this.parse(source);
    return {
      ast,
      literal: evaluateLiteral(ast),
      operational: evaluateOperational(ast),
    };
  }

  /**
   * Pretty print evaluation results
   */
  static prettyPrint(source: string): string {
    const { literal, operational } = this.evaluate(source);

    let output = `Expression: ${source}\n\n`;

    output += `Literal Backend (Bytes):\n`;
    output += `  ${this.formatBytes(literal.bytes)}\n`;
    if (literal.addresses) {
      output += `  Addresses: ${this.formatAddresses(literal.addresses)}\n`;
    }

    output += `\nOperational Backend (Words):\n`;
    output += this.formatWords(operational.words);

    return output;
  }

  // ==========================================================================
  // Formatting Utilities
  // ==========================================================================

  /**
   * Format bytes as hex string
   */
  static formatBytes(bytes: number[]): string {
    return formatBytes(bytes);
  }

  /**
   * Format addresses
   */
  static formatAddresses(addresses: number[]): string {
    return formatAddresses(addresses);
  }

  /**
   * Format words with indentation
   */
  static formatWords(words: string[], indent: number = 2): string {
    return formatWords(words, indent);
  }

  // ==========================================================================
  // Class Utilities
  // ==========================================================================

  /**
   * Get class information for a byte
   */
  static classInfo(byte: number): ClassInfo {
    return getClassInfo(byte);
  }

  /**
   * Get class index from byte
   */
  static classIndex(byte: number): number {
    return byteToClassIndex(byte);
  }

  /**
   * Get canonical byte for a class
   */
  static canonicalByte(classIndex: number): number {
    return classIndexToCanonicalByte(classIndex);
  }

  /**
   * Test if two bytes are equivalent under ≡₉₆
   */
  static equivalent(byte1: number, byte2: number): boolean {
    return areEquivalent(byte1, byte2);
  }

  /**
   * Get all bytes in an equivalence class
   */
  static equivalenceClass(classIndex: number): number[] {
    return getEquivalenceClass(classIndex);
  }

  /**
   * Format class info as string
   */
  static formatClass(byte: number): string {
    return formatClassInfo(getClassInfo(byte));
  }

  // ==========================================================================
  // Belt Utilities
  // ==========================================================================

  /**
   * Compute belt address from page and byte
   */
  static beltAddress(page: number, byte: number): BeltAddress {
    return computeBeltAddress(page, byte);
  }

  /**
   * Decompose belt address into page and byte
   */
  static decodeBeltAddress(address: number): BeltAddress {
    return decomposeBeltAddress(address);
  }

  // ==========================================================================
  // Introspection
  // ==========================================================================

  /**
   * Get all 96 class indices with their canonical bytes
   */
  static allClasses(): { index: number; byte: number }[] {
    const result: { index: number; byte: number }[] = [];
    for (let i = 0; i < 96; i++) {
      result.push({
        index: i,
        byte: classIndexToCanonicalByte(i),
      });
    }
    return result;
  }

  /**
   * Get all 256 bytes mapped to their classes
   */
  static byteClassMapping(): { byte: number; classIndex: number }[] {
    const result: { byte: number; classIndex: number }[] = [];
    for (let byte = 0; byte < 256; byte++) {
      result.push({
        byte,
        classIndex: byteToClassIndex(byte),
      });
    }
    return result;
  }
}

export default Atlas;
