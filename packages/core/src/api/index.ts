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
  applyDTransformToClass,
  getTrialityOrbit,
  getAllTrialityOrbits,
} from '../class-system';
import type {
  Phrase,
  LiteralResult,
  OperationalResult,
  ClassInfo,
  BeltAddress,
  DTransformResult,
  TrialityOrbit,
} from '../types';
import * as SGA from '../sga';
import * as Bridge from '../bridge';

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

  /**
   * Apply D-transform to a class index
   *
   * @param classIndex - Starting class (0-95)
   * @param k - Triality rotation amount (will be normalized to 0-2)
   * @returns Result object with old/new class and transformation details
   *
   * @example
   * const result = Atlas.applyDTransform(21, 1);
   * console.log(result.newClass); // 5
   * console.log(result.transformation); // { h2: 0, d_old: 2, d_new: 0, l: 5 }
   */
  static applyDTransform(classIndex: number, k: number): DTransformResult {
    return applyDTransformToClass(classIndex, k);
  }

  /**
   * Get triality orbit for a class
   * Returns all 3 classes with same (h₂, ℓ) but different d
   *
   * @param classIndex - Any class in the orbit (0-95)
   * @returns TrialityOrbit containing all 3 classes
   *
   * @example
   * const orbit = Atlas.getTrialityOrbit(21);
   * console.log(orbit.classes); // [5, 13, 21]
   * console.log(orbit.baseCoordinates); // { h2: 0, l: 5 }
   */
  static getTrialityOrbit(classIndex: number): TrialityOrbit {
    return getTrialityOrbit(classIndex);
  }

  /**
   * Get all 32 triality orbits
   * Each orbit contains 3 classes (96 classes / 3 = 32 orbits)
   *
   * @returns Array of 32 TrialityOrbit objects
   *
   * @example
   * const orbits = Atlas.getAllTrialityOrbits();
   * console.log(orbits.length); // 32
   * console.log(orbits[0].classes); // [0, 8, 16]
   */
  static getAllTrialityOrbits(): TrialityOrbit[] {
    return getAllTrialityOrbits();
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

  // ==========================================================================
  // SGA (Sigmatics Geometric Algebra) - v0.3.0
  // ==========================================================================

  /**
   * SGA namespace provides access to the Sigmatics Geometric Algebra
   *
   * SGA = Cl₀,₇ ⊗ ℝ[ℤ₄] ⊗ ℝ[ℤ₃]
   *
   * This is the formal algebraic foundation beneath the 96-class system,
   * enabling:
   * - Verification of transform correctness via commutative diagrams
   * - Extension to higher-grade elements (bivectors, trivectors)
   * - Geometric semantics via the octonion channel
   * - Complete algebraic automorphism implementations of R/D/T/M
   *
   * @example
   * // Lift a class to SGA
   * const element = Atlas.SGA.lift(21);
   *
   * // Apply transforms
   * const transformed = Atlas.SGA.D(element);
   *
   * // Project back to class
   * const newClass = Atlas.SGA.project(transformed);
   * console.log(newClass); // 5
   *
   * // Octonion multiplication
   * const u = Atlas.SGA.Octonion.randomOctonion();
   * const v = Atlas.SGA.Octonion.randomOctonion();
   * const product = Atlas.SGA.Octonion.cayleyProduct(u, v);
   */
  static SGA = {
    // Core SGA operations
    ...SGA,

    // Bridge operations
    lift: Bridge.lift,
    liftAll: Bridge.liftAll,
    project: Bridge.project,
    isRank1: Bridge.isRank1,

    // Validation
    validate: Bridge.validateAll,
    validateR: Bridge.validateR,
    validateD: Bridge.validateD,
    validateT: Bridge.validateT,
    validateM: Bridge.validateM,

    // Convenience wrappers for transforms
    R: (element: SGA.SgaElement, k = 1) => {
      if (!element || typeof element !== 'object' || !element.clifford || !element.z4 || !element.z3) {
        throw new Error(
          'R transform expects an SGA element. Use Atlas.SGA.lift(classIndex) to create one, or Atlas.SGA.createSgaElement()',
        );
      }
      return SGA.transformRPower(element, k);
    },
    D: (element: SGA.SgaElement, k = 1) => {
      if (!element || typeof element !== 'object' || !element.clifford || !element.z4 || !element.z3) {
        throw new Error(
          'D transform expects an SGA element. Use Atlas.SGA.lift(classIndex) to create one, or Atlas.SGA.createSgaElement()',
        );
      }
      return SGA.transformDPower(element, k);
    },
    T: (element: SGA.SgaElement, k = 1) => {
      if (!element || typeof element !== 'object' || !element.clifford || !element.z4 || !element.z3) {
        throw new Error(
          'T transform expects an SGA element. Use Atlas.SGA.lift(classIndex) to create one, or Atlas.SGA.createSgaElement()',
        );
      }
      return SGA.transformTPower(element, k);
    },
    M: (element: SGA.SgaElement) => {
      if (!element || typeof element !== 'object' || !element.clifford || !element.z4 || !element.z3) {
        throw new Error(
          'M transform expects an SGA element. Use Atlas.SGA.lift(classIndex) to create one, or Atlas.SGA.createSgaElement()',
        );
      }
      return SGA.transformM(element);
    },

    // Octonion channel
    Octonion: {
      cayleyProduct: SGA.cayleyProduct,
      innerProduct: SGA.octonionInnerProduct,
      crossProduct: SGA.vectorCrossProduct,
      conjugate: SGA.octonionConjugate,
      norm: SGA.octonionNorm,
      normSquared: SGA.octonionNormSquared,
      verifyAlternativity: SGA.verifyAlternativity,
      verifyNormMultiplicativity: SGA.verifyNormMultiplicativity,
      randomOctonion: SGA.randomOctonion,
    },

    // Fano plane
    Fano: {
      lines: SGA.FANO_LINES,
      crossProduct: SGA.crossProduct,
      verify: SGA.verifyFanoPlane,
      getLinesContaining: SGA.getLinesContaining,
      isFanoLine: SGA.isFanoLine,
    },
  };
}

export default Atlas;
