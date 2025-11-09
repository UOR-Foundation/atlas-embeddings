/**
 * Atlas Class Utilities
 * Implements the authoritative ≡₉₆ mapping
 */

import type {
  SigilComponents,
  ClassInfo,
  BeltAddress,
  DTransformResult,
  TrialityOrbit,
} from '../types';

// ============================================================================
// Authoritative Class Mapping (≡₉₆)
// ============================================================================

/**
 * Decode byte to (h₂, d, ℓ) components
 * Formula from spec:
 * - h₂ = (b7<<1) | b6 ∈ {0..3}
 * - d₄₅: 0 if (b4,b5)=(0,0); 1 if (1,0); 2 if (0,1)
 * - low₃ = (b3<<2)|(b2<<1)|b1 ∈ {0..7}
 */
export function decodeByteToComponents(byte: number): SigilComponents {
  const b = byte & 0xff;
  const b7 = (b >> 7) & 1;
  const b6 = (b >> 6) & 1;
  const b5 = (b >> 5) & 1;
  const b4 = (b >> 4) & 1;
  const b3 = (b >> 3) & 1;
  const b2 = (b >> 2) & 1;
  const b1 = (b >> 1) & 1;

  const h2 = ((b7 << 1) | b6) as 0 | 1 | 2 | 3;

  let d: 0 | 1 | 2;
  if (b4 === 0 && b5 === 0) d = 0;
  else if (b4 === 1 && b5 === 0) d = 1;
  else if (b4 === 0 && b5 === 1) d = 2;
  else d = 0; // (1,1) falls back to 0 per spec

  const l = ((b3 << 2) | (b2 << 1) | b1) as 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7;

  return { h2, d, l };
}

/**
 * Compute class index from components
 * class = 24*h₂ + 8*d + ℓ
 */
export function componentsToClassIndex(comp: SigilComponents): number {
  return 24 * comp.h2 + 8 * comp.d + comp.l;
}

/**
 * Compute class index directly from byte
 */
export function byteToClassIndex(byte: number): number {
  const comp = decodeByteToComponents(byte);
  return componentsToClassIndex(comp);
}

/**
 * Decode class index to components
 */
export function decodeClassIndex(classIndex: number): SigilComponents {
  if (classIndex < 0 || classIndex > 95) {
    throw new Error(`Class index ${classIndex} out of range [0..95]`);
  }

  const h2 = Math.floor(classIndex / 24) as 0 | 1 | 2 | 3;
  const remainder = classIndex % 24;
  const d = Math.floor(remainder / 8) as 0 | 1 | 2;
  const l = (remainder % 8) as 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7;

  return { h2, d, l };
}

/**
 * Encode components to canonical byte (b0=0)
 * Maps d={0,1,2} to (b4,b5)={00,10,01}
 */
export function encodeComponentsToByte(comp: SigilComponents): number {
  const { h2, d, l } = comp;

  // Extract bit components
  const b7 = (h2 >> 1) & 1;
  const b6 = h2 & 1;

  // Map modality to (b4, b5)
  let b5: number, b4: number;
  switch (d) {
    case 0:
      b4 = 0;
      b5 = 0;
      break;
    case 1:
      b4 = 1;
      b5 = 0;
      break;
    case 2:
      b4 = 0;
      b5 = 1;
      break;
  }

  const b3 = (l >> 2) & 1;
  const b2 = (l >> 1) & 1;
  const b1 = l & 1;
  const b0 = 0; // canonical form

  return (b7 << 7) | (b6 << 6) | (b5 << 5) | (b4 << 4) | (b3 << 3) | (b2 << 2) | (b1 << 1) | b0;
}

/**
 * Get canonical representative byte for a class index
 */
export function classIndexToCanonicalByte(classIndex: number): number {
  const comp = decodeClassIndex(classIndex);
  return encodeComponentsToByte(comp);
}

/**
 * Get full class info for a byte
 */
export function getClassInfo(byte: number): ClassInfo {
  const components = decodeByteToComponents(byte);
  const classIndex = componentsToClassIndex(components);
  const canonicalByte = classIndexToCanonicalByte(classIndex);

  return { classIndex, components, canonicalByte };
}

// ============================================================================
// Transform Operations
// ============================================================================

/**
 * Apply rotation transform R±k (mod 4 on h₂)
 */
export function applyRotation(comp: SigilComponents, k: number): SigilComponents {
  const h2 = ((((comp.h2 + k) % 4) + 4) % 4) as 0 | 1 | 2 | 3;
  return { ...comp, h2 };
}

/**
 * Apply twist transform T±k (mod 8 on ℓ)
 */
export function applyTwist(comp: SigilComponents, k: number): SigilComponents {
  const l = ((((comp.l + k) % 8) + 8) % 8) as 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7;
  return { ...comp, l };
}

/**
 * Apply mirror transform M (flip modality: 1↔2, 0→0)
 */
export function applyMirror(comp: SigilComponents): SigilComponents {
  let d: 0 | 1 | 2;
  switch (comp.d) {
    case 0:
      d = 0;
      break;
    case 1:
      d = 2;
      break;
    case 2:
      d = 1;
      break;
  }
  return { ...comp, d };
}

/**
 * Apply triality transform D±k (mod 3 on d)
 * D+k: (h₂, d, ℓ) ↦ (h₂, (d+k) mod 3, ℓ)
 *
 * Preserves h₂ and ℓ, rotates modality:
 * - D+1: 0→1, 1→2, 2→0
 * - D+2: 0→2, 2→1, 1→0 (same as D-1)
 * - D+3: identity
 */
export function applyTriality(comp: SigilComponents, k: number): SigilComponents {
  // Normalize k to [0, 2] range
  const normalized = ((k % 3) + 3) % 3;

  // Apply modality rotation
  const d = ((comp.d + normalized) % 3) as 0 | 1 | 2;

  return { ...comp, d };
}

/**
 * Apply all transforms in sequence
 */
export function applyTransforms(
  comp: SigilComponents,
  transforms: { R?: number; D?: number; T?: number; M?: boolean },
): SigilComponents {
  let result = comp;

  // Apply in order: R, D, T (commutative group), then M
  // Order doesn't matter for R, D, T since they act on independent components
  if (transforms.R !== undefined) {
    result = applyRotation(result, transforms.R);
  }
  if (transforms.D !== undefined) {
    result = applyTriality(result, transforms.D);
  }
  if (transforms.T !== undefined) {
    result = applyTwist(result, transforms.T);
  }
  if (transforms.M) {
    result = applyMirror(result);
  }

  return result;
}

// ============================================================================
// Belt Addressing
// ============================================================================

/**
 * Compute belt address from page and byte
 * addr = 256*λ + byte
 */
export function computeBeltAddress(page: number, byte: number): BeltAddress {
  if (page < 0 || page > 47) {
    throw new Error(`Page ${page} out of range [0..47]`);
  }
  if (byte < 0 || byte > 255) {
    throw new Error(`Byte ${byte} out of range [0..255]`);
  }

  return {
    page,
    byte,
    address: 256 * page + byte,
  };
}

/**
 * Decompose belt address into page and byte
 */
export function decomposeBeltAddress(address: number): BeltAddress {
  if (address < 0 || address > 12287) {
    throw new Error(`Address ${address} out of range [0..12287]`);
  }

  const page = Math.floor(address / 256);
  const byte = address % 256;

  return { page, byte, address };
}

// ============================================================================
// Equivalence Testing
// ============================================================================

/**
 * Test if two bytes are equivalent under ≡₉₆
 */
export function areEquivalent(byte1: number, byte2: number): boolean {
  return byteToClassIndex(byte1) === byteToClassIndex(byte2);
}

/**
 * Get all bytes in the same equivalence class
 */
export function getEquivalenceClass(classIndex: number): number[] {
  const result: number[] = [];
  for (let byte = 0; byte < 256; byte++) {
    if (byteToClassIndex(byte) === classIndex) {
      result.push(byte);
    }
  }
  return result;
}

// ============================================================================
// Pretty Printing
// ============================================================================

/**
 * Format components as (h₂, d, ℓ)
 */
export function formatComponents(comp: SigilComponents): string {
  return `(h₂=${comp.h2}, d=${comp.d}, ℓ=${comp.l})`;
}

/**
 * Format modality as symbol
 */
export function formatModality(d: 0 | 1 | 2): string {
  switch (d) {
    case 0:
      return '•'; // neutral
    case 1:
      return '▲'; // produce (clockwise)
    case 2:
      return '▼'; // consume (counter-clockwise)
  }
}

/**
 * Format class info
 */
export function formatClassInfo(info: ClassInfo): string {
  return `c${info.classIndex.toString().padStart(2, '0')} ${formatComponents(info.components)} → 0x${info.canonicalByte.toString(16).toUpperCase().padStart(2, '0')}`;
}

// ============================================================================
// Triality Orbits
// ============================================================================

/**
 * Apply D-transform to a class index
 * @param classIndex - Starting class (0-95)
 * @param k - Rotation amount (will be normalized to 0-2)
 * @returns New class index after D-transform
 */
export function applyDTransformToClass(classIndex: number, k: number): DTransformResult {
  if (classIndex < 0 || classIndex >= 96) {
    throw new Error(`Invalid class index: ${classIndex}`);
  }

  // Get components
  const components = decodeClassIndex(classIndex);
  const { h2, d, l } = components;

  // Apply triality
  const transformed = applyTriality(components, k);
  const d_new = transformed.d;

  // Calculate new class index
  const newClass = componentsToClassIndex(transformed);

  return {
    oldClass: classIndex,
    newClass,
    transformation: {
      h2,
      d_old: d,
      d_new,
      l,
    },
  };
}

/**
 * Get triality orbit containing a class
 * Returns all 3 classes in the orbit with same (h₂, ℓ) but different d
 *
 * @param classIndex - Any class in the orbit
 * @returns TrialityOrbit with all 3 classes
 */
export function getTrialityOrbit(classIndex: number): TrialityOrbit {
  const components = decodeClassIndex(classIndex);
  const { h2, l } = components;

  // Generate all 3 classes in orbit
  const classes: [number, number, number] = [
    componentsToClassIndex({ h2, d: 0, l }),
    componentsToClassIndex({ h2, d: 1, l }),
    componentsToClassIndex({ h2, d: 2, l }),
  ];

  return {
    baseCoordinates: { h2, l },
    classes,
  };
}

/**
 * Generate all 32 triality orbits
 * Each orbit contains 3 classes (96 classes / 3 = 32 orbits)
 */
export function getAllTrialityOrbits(): TrialityOrbit[] {
  const orbits: TrialityOrbit[] = [];

  for (let h2 = 0; h2 < 4; h2++) {
    for (let l = 0; l < 8; l++) {
      orbits.push({
        baseCoordinates: {
          h2: h2 as 0 | 1 | 2 | 3,
          l: l as 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7,
        },
        classes: [24 * h2 + 8 * 0 + l, 24 * h2 + 8 * 1 + l, 24 * h2 + 8 * 2 + l],
      });
    }
  }

  return orbits;
}
