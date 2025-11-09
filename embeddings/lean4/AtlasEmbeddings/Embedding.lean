/-
Copyright (c) 2025 UOR Foundation. All rights reserved.
Released under MIT license.

# Atlas → E₈ Embedding - Phase 4 (Minimal)

The canonical embedding of 96 Atlas vertices into 240 E₈ roots.
From Rust: `src/embedding/mod.rs` lines 298-467

**NO `sorry` POLICY** - No theorems in minimal version.
**Verification Strategy**: Runtime verification (matches Rust approach).
-/

import AtlasEmbeddings.Atlas
import AtlasEmbeddings.E8

/-! ## The Certified Embedding

From Rust (lines 460-467):
The CERTIFIED_EMBEDDING is a lookup table mapping Atlas vertex index (0..96)
to E₈ root index (0..240).

This embedding was discovered via computational search and certified to satisfy:
1. Injectivity: 96 distinct roots
2. Adjacency preservation: edges → inner product -1
3. Sign classes: exactly 48 pairs {r, -r}

The embedding is unique up to E₈ Weyl group symmetry.
-/

/-- Certified embedding from tier_a_certificate.json -/
def certifiedEmbedding : List Nat := [
  0, 4, 1, 3, 7, 5, 2, 6, 11, 10, 9, 8, 12, 14, 13, 15, 19, 18, 16, 17,
  23, 21, 20, 22, 24, 28, 25, 27, 31, 29, 26, 30, 35, 34, 33, 32, 36, 38,
  37, 39, 43, 42, 40, 41, 47, 45, 44, 46, 48, 52, 49, 51, 55, 53, 50, 54,
  59, 58, 57, 56, 60, 62, 61, 63, 67, 66, 64, 65, 71, 69, 68, 70, 72, 76,
  73, 75, 79, 77, 74, 78, 83, 82, 81, 80, 84, 86, 85, 87, 91, 90, 88, 89,
  95, 93, 92, 94
]

/-! ## The Embedding Function

Maps Atlas labels to E₈ roots via the certified lookup table.
-/

/-- Map Atlas vertex index to E₈ root index -/
def atlasToE8Index (v : Fin 96) : Nat :=
  certifiedEmbedding[v.val]!

/-- Map Atlas label to E₈ root vector using Fin 96 index -/
def atlasToE8ByIndex (v : Fin 96) : Vector8 :=
  let e8Idx := certifiedEmbedding[v.val]!
  allE8Roots[e8Idx]!

/-! ## Verification Functions (following Rust pattern)

From Rust (lines 367-444):
The Rust implementation provides verification methods:
- verify_injective(): checks all 96 vertices map to distinct roots
- verify_root_norms(): checks all embedded roots have norm² = 2
- count_sign_classes(): counts pairs {r, -r} (should be 48)

These are runtime checks, not compile-time proofs. Following the Rust
model and minimal progress strategy, we define these as computable
functions without proving theorems about them yet.
-/

/-- Check if embedding is injective (all 96 roots distinct) -/
def verifyInjective : Bool :=
  certifiedEmbedding.length = 96 &&
  certifiedEmbedding.toFinset.card = 96

/-- Count how many embedded roots we have -/
def embeddingSize : Nat :=
  certifiedEmbedding.length

/-! ## Count Verification

Following Rust's approach (lines 442-444): runtime verification via
`verify_all()` checks injectivity, norms, and sign classes.

Lean's compile-time proof would require computing all properties at
type-checking time. Following minimal progress strategy, we generate
the embedding computationally without compile-time proofs.
-/
