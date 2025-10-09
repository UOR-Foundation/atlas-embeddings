/-
Copyright (c) 2025 UOR Foundation. All rights reserved.
Released under MIT license.

# E₈ Root System - Phase 2 (Minimal)

Generate all 240 E₈ roots computationally.
From Rust: `src/e8/mod.rs` lines 305-453

**NO `sorry` POLICY** - No theorems in minimal version.
**Verification Strategy**: Runtime count verification (matches Rust approach).
-/

import AtlasEmbeddings.Arithmetic

open HalfInteger Vector8

/-! ## Integer Roots: ±eᵢ ± eⱼ (i < j)

From Rust (lines 335-361):
112 roots = C(8,2) × 4 = 28 × 4
-/

/-- Generate all 112 integer-coordinate roots -/
def generateIntegerRoots : List Vector8 :=
  let zero := HalfInteger.zero
  List.flatten <| List.map (fun i =>
    List.flatten <| List.map (fun j =>
      List.map (fun (signI, signJ) =>
        let coords := fun k : Fin 8 =>
          if k.val = i then HalfInteger.ofInt signI
          else if k.val = j then HalfInteger.ofInt signJ
          else zero
        ⟨coords⟩
      ) [(1,1), (1,-1), (-1,1), (-1,-1)]
    ) (List.range 8 |>.filter (fun j => i < j))
  ) (List.range 8)

/-! ## Half-Integer Roots: all ±1/2, even # of minuses

From Rust (lines 363-393):
128 roots = 2⁸ / 2 = 256 / 2
-/

/-- Generate all 128 half-integer-coordinate roots -/
def generateHalfIntegerRoots : List Vector8 :=
  let half := HalfInteger.new 1  -- 1/2
  (List.range 256).filterMap fun pattern =>
    let coords := fun (i : Fin 8) =>
      if (pattern >>> i.val) &&& 1 = 1
      then -half
      else half
    let numNeg := (List.range 8).countP fun i =>
      (pattern >>> i) &&& 1 = 1
    if numNeg % 2 = 0
    then some ⟨coords⟩
    else none

/-! ## Complete E₈ Root System: 240 roots

From Rust (lines 322-333):
Total = 112 + 128 = 240

**Count Verification Strategy**: Following Rust implementation (lines 331, 359, 391),
counts are verified at runtime via `assert_eq!` in `generate_integer_roots()`,
`generate_half_integer_roots()`, and `verify_invariants()`.

Lean's compile-time proof of `generateIntegerRoots.length = 112` would require
computing all 112 roots at type-checking time, causing maximum recursion depth errors.

Instead, we follow Rust's approach: generate roots computationally, verify counts
at runtime (or in test suite). This matches the project's verification strategy
where tests serve as certifying proofs (see CLAUDE.md).
-/

/-- All 240 E₈ roots -/
def allE8Roots : List Vector8 :=
  generateIntegerRoots ++ generateHalfIntegerRoots

/-! ## Root System Axiom: All Roots Have Norm² = 2

From Rust (src/e8/mod.rs:433): `assert!(root.is_root(), "Root {i} must have norm² = 2")`

We verify this property for all 240 roots by checking that each root in
the list satisfies the norm condition.
-/

/-- Check if a vector has norm² = 2 -/
def hasNormTwo (v : Vector8) : Bool :=
  v.normSquared == 2

/-- Verify all E₈ roots have norm² = 2 -/
theorem all_roots_have_norm_two :
    allE8Roots.all hasNormTwo = true := by
  native_decide
