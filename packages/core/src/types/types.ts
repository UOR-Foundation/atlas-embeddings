/**
 * Atlas Core Types
 * Based on formal specification v1.0
 */

// ============================================================================
// Class Sigil (h₂, d, ℓ) triple
// ============================================================================

export type ScopeQuadrant = 0 | 1 | 2 | 3; // h₂ - cardinal direction
export type Modality = 0 | 1 | 2; // d - neutral, produce, consume
export type ContextSlot = 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7; // ℓ - 8-ring position

export interface ClassSigil {
  kind: 'Sigil';
  classIndex: number; // 0..95
  rotate?: number; // R±k transform
  triality?: number; // D±k transform
  twist?: number; // T±k transform
  mirror?: boolean; // M transform
  page?: number; // λ ∈ {0..47} optional belt page
}

// ============================================================================
// Seven Generators
// ============================================================================

export type GeneratorName = 'mark' | 'copy' | 'swap' | 'merge' | 'split' | 'quote' | 'evaluate';

export interface Operation {
  kind: 'Op';
  generator: GeneratorName;
  sigil: ClassSigil;
}

// ============================================================================
// Composition Structure
// ============================================================================

export interface Sequential {
  kind: 'Seq';
  items: Term[]; // right-to-left: last item executes first
}

export interface Parallel {
  kind: 'Par';
  branches: Sequential[];
}

export interface Transform {
  R?: number; // rotate quadrants (mod 4)
  D?: number; // triality rotation (mod 3)
  T?: number; // twist context ring (mod 8)
  M?: boolean; // mirror modality
}

export interface Transformed {
  kind: 'Xform';
  transform: Transform;
  body: Parallel;
}

export interface Group {
  kind: 'Group';
  body: Parallel;
}

export type Term = Operation | Group | Transformed;
export type Phrase = Transformed | Parallel;

// ============================================================================
// Decoded Sigil Components
// ============================================================================

export interface SigilComponents {
  h2: ScopeQuadrant;
  d: Modality;
  l: ContextSlot;
}

// ============================================================================
// Evaluation Results
// ============================================================================

export interface LiteralResult {
  bytes: number[]; // canonical byte representatives
  addresses?: number[]; // belt addresses if pages specified
}

export interface OperationalResult {
  words: string[]; // lowered generator words
}

// ============================================================================
// Parser Result
// ============================================================================

export type ParseResult<T> =
  | { success: true; value: T; rest: string }
  | { success: false; error: string; position: number };

// ============================================================================
// Class Mapping
// ============================================================================

export interface ClassInfo {
  classIndex: number; // 0..95
  components: SigilComponents;
  canonicalByte: number; // with b0=0
}

// ============================================================================
// Budget and Resonance
// ============================================================================

export interface Budget {
  allocated: number;
  consumed: number;
  remaining: number;
}

export interface ResonanceState {
  class: number; // 0..95
  budget: Budget;
  phase: 'compile' | 'run' | 'verify';
}

// ============================================================================
// Belt and Page Structure
// ============================================================================

export interface BeltAddress {
  page: number; // λ ∈ {0..47}
  byte: number; // 0..255
  address: number; // 256*λ + byte ∈ {0..12287}
}

export interface PageState {
  index: number; // 0..47
  bytes: Uint8Array; // 256 bytes
  classes: number[]; // 256 class indices
}

// ============================================================================
// Triality (D-Transform)
// ============================================================================

/**
 * Triality orbit containing 3 classes with same (h₂, ℓ) but different d
 */
export interface TrialityOrbit {
  baseCoordinates: { h2: ScopeQuadrant; l: ContextSlot };
  classes: [number, number, number]; // [d=0, d=1, d=2]
}

/**
 * Result of applying D-transform
 */
export interface DTransformResult {
  oldClass: number;
  newClass: number;
  transformation: {
    h2: ScopeQuadrant;
    d_old: Modality;
    d_new: Modality;
    l: ContextSlot;
  };
}
