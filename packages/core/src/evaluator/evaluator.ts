/**
 * Atlas Evaluator
 * Implements both literal (byte) and operational (word) backends
 */

import type {
  ClassSigil,
  Operation,
  Sequential,
  Term,
  Phrase,
  LiteralResult,
  OperationalResult,
  Transform,
} from '../types';
import {
  decodeClassIndex,
  applyTransforms,
  encodeComponentsToByte,
  computeBeltAddress,
} from '../class-system';

// ============================================================================
// Literal Backend - Byte Semantics
// ============================================================================

/**
 * Evaluate phrase to canonical bytes and optional belt addresses
 */
export function evaluateLiteral(phrase: Phrase): LiteralResult {
  const collected = collectLiteralLeaves(phrase);

  return {
    bytes: collected.bytes,
    addresses: collected.addresses.length > 0 ? collected.addresses : undefined,
  };
}

interface CollectedLeaves {
  bytes: number[];
  addresses: number[];
}

/**
 * Collect all leaf sigils, applying transforms and computing bytes
 */
function collectLiteralLeaves(
  node: Phrase | Term | Sequential | ClassSigil,
  outerTransform?: Transform,
): CollectedLeaves {
  const result: CollectedLeaves = { bytes: [], addresses: [] };

  if ('kind' in node) {
    switch (node.kind) {
      case 'Xform': {
        // Combine outer and local transforms
        const combinedTransform = combineTransforms(outerTransform, node.transform);
        const inner = collectLiteralLeaves(node.body, combinedTransform);
        result.bytes.push(...inner.bytes);
        result.addresses.push(...inner.addresses);
        break;
      }

      case 'Par': {
        // Process all branches
        for (const branch of node.branches) {
          const inner = collectLiteralLeaves(branch, outerTransform);
          result.bytes.push(...inner.bytes);
          result.addresses.push(...inner.addresses);
        }
        break;
      }

      case 'Seq': {
        // Process all items in sequence
        for (const item of node.items) {
          const inner = collectLiteralLeaves(item, outerTransform);
          result.bytes.push(...inner.bytes);
          result.addresses.push(...inner.addresses);
        }
        break;
      }

      case 'Group': {
        const inner = collectLiteralLeaves(node.body, outerTransform);
        result.bytes.push(...inner.bytes);
        result.addresses.push(...inner.addresses);
        break;
      }

      case 'Op': {
        // Leaf node - evaluate the sigil
        const { byte, address } = evaluateSigil(node.sigil, outerTransform);
        result.bytes.push(byte);
        if (address !== undefined) {
          result.addresses.push(address);
        }
        break;
      }

      case 'Sigil': {
        // Should not appear standalone, but handle it
        const { byte, address } = evaluateSigil(node, outerTransform);
        result.bytes.push(byte);
        if (address !== undefined) {
          result.addresses.push(address);
        }
        break;
      }
    }
  }

  return result;
}

/**
 * Evaluate a single sigil to byte and optional address
 */
function evaluateSigil(
  sigil: ClassSigil,
  outerTransform?: Transform,
): { byte: number; address?: number } {
  // Start with base components
  let components = decodeClassIndex(sigil.classIndex);

  // Apply sigil's own transforms (postfix)
  if (
    sigil.rotate !== undefined ||
    sigil.triality !== undefined ||
    sigil.twist !== undefined ||
    sigil.mirror
  ) {
    components = applyTransforms(components, {
      R: sigil.rotate,
      D: sigil.triality,
      T: sigil.twist,
      M: sigil.mirror,
    });
  }

  // Apply outer transforms (prefix)
  if (outerTransform) {
    components = applyTransforms(components, outerTransform);
  }

  // Encode to canonical byte
  const byte = encodeComponentsToByte(components);

  // Compute belt address if page is specified
  let address: number | undefined;
  if (sigil.page !== undefined) {
    address = computeBeltAddress(sigil.page, byte).address;
  }

  return { byte, address };
}

/**
 * Combine outer and inner transforms
 */
function combineTransforms(outer?: Transform, inner?: Transform): Transform | undefined {
  if (!outer && !inner) return undefined;
  if (!outer) return inner;
  if (!inner) return outer;

  return {
    R: (outer.R || 0) + (inner.R || 0),
    D: (outer.D || 0) + (inner.D || 0),
    T: (outer.T || 0) + (inner.T || 0),
    M: !!(outer.M !== inner.M), // XOR for mirror
  };
}

// ============================================================================
// Operational Backend - Word Semantics
// ============================================================================

/**
 * Evaluate phrase to generator words
 */
export function evaluateOperational(phrase: Phrase): OperationalResult {
  const words = lowerToWords(phrase);
  return { words };
}

/**
 * Lower AST to flat list of generator words
 */
function lowerToWords(node: Phrase | Term | Sequential, outerTransform?: Transform): string[] {
  const result: string[] = [];

  if ('kind' in node) {
    switch (node.kind) {
      case 'Xform': {
        // Apply transform by inserting control words
        const combinedTransform = combineTransforms(outerTransform, node.transform);
        if (combinedTransform) {
          result.push(...encodeTransform(combinedTransform, true)); // enter
        }
        result.push(...lowerToWords(node.body, combinedTransform));
        if (combinedTransform) {
          result.push(...encodeTransform(combinedTransform, false)); // exit
        }
        break;
      }

      case 'Par': {
        // Monoidal product - only emit markers when there is real parallelism
        if (node.branches.length === 1) {
          result.push(...lowerToWords(node.branches[0], outerTransform));
        } else {
          result.push('⊗_begin');
          for (let i = 0; i < node.branches.length; i++) {
            if (i > 0) result.push('⊗_sep');
            result.push(...lowerToWords(node.branches[i], outerTransform));
          }
          result.push('⊗_end');
        }
        break;
      }

      case 'Seq': {
        // Sequential composition - rightmost first
        for (let i = node.items.length - 1; i >= 0; i--) {
          result.push(...lowerToWords(node.items[i], outerTransform));
        }
        break;
      }

      case 'Group': {
        result.push(...lowerToWords(node.body, outerTransform));
        break;
      }

      case 'Op': {
        // Lower operation to words
        result.push(...lowerOperation(node, outerTransform));
        break;
      }
    }
  }

  return result;
}

/**
 * Lower a single operation to words
 */
function lowerOperation(op: Operation, outerTransform?: Transform): string[] {
  // Compute effective components
  let components = decodeClassIndex(op.sigil.classIndex);

  if (
    op.sigil.rotate !== undefined ||
    op.sigil.triality !== undefined ||
    op.sigil.twist !== undefined ||
    op.sigil.mirror
  ) {
    components = applyTransforms(components, {
      R: op.sigil.rotate,
      D: op.sigil.triality,
      T: op.sigil.twist,
      M: op.sigil.mirror,
    });
  }

  if (outerTransform) {
    components = applyTransforms(components, outerTransform);
  }

  // Format generator with parameters
  const words: string[] = [];

  switch (op.generator) {
    case 'mark':
      words.push(`mark`);
      break;

    case 'copy':
      words.push(`copy[d=${components.d}]`);
      break;

    case 'swap':
      words.push(`swap`);
      break;

    case 'merge':
      words.push(`merge[d=${components.d}]`);
      break;

    case 'split':
      words.push(`split[ℓ=${components.l}]`);
      break;

    case 'quote':
      words.push(`quote[ℓ=${components.l}]`);
      break;

    case 'evaluate':
      words.push(`phase[h₂=${components.h2}]`, `evaluate`);
      break;
  }

  return words;
}

/**
 * Encode transform as control words
 */
function encodeTransform(transform: Transform, enter: boolean): string[] {
  const words: string[] = [];
  const prefix = enter ? '→' : '←';

  if (transform.R !== undefined && transform.R !== 0) {
    words.push(`${prefix}ρ[${transform.R}]`);
  }
  if (transform.D !== undefined && transform.D !== 0) {
    const normalized = ((transform.D % 3) + 3) % 3;
    words.push(`${prefix}δ[${normalized}]`);
  }
  if (transform.T !== undefined && transform.T !== 0) {
    words.push(`${prefix}τ[${transform.T}]`);
  }
  if (transform.M) {
    words.push(`${prefix}μ`);
  }

  return words;
}

// ============================================================================
// Utilities
// ============================================================================

/**
 * Format bytes as hex string
 */
export function formatBytes(bytes: number[]): string {
  return bytes.map((b) => '0x' + b.toString(16).toUpperCase().padStart(2, '0')).join(' ');
}

/**
 * Format addresses
 */
export function formatAddresses(addresses: number[]): string {
  return addresses.map((a) => a.toString()).join(', ');
}

/**
 * Format words with indentation
 */
export function formatWords(words: string[], indent: number = 2): string {
  const space = ' '.repeat(indent);
  return words.map((w) => space + w).join('\n');
}
