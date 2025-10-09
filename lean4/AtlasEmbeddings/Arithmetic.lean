/-
Copyright (c) 2025 UOR Foundation. All rights reserved.
Released under MIT license.

# Exact Rational Arithmetic - Phases 1.1 & 1.2

Phase 1.1: HalfInteger (lines 48-213)
Phase 1.2: Vector8 (lines 215-372)
From Rust: `src/arithmetic/mod.rs`

**NO `sorry` POLICY** - All 4 theorems proven.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open BigOperators

/-! ## HalfInteger: n/2 where n ∈ ℤ

From Rust (line 68-71):
```rust
pub struct HalfInteger {
    numerator: i64,
}
```
-/

structure HalfInteger where
  numerator : ℤ
  deriving DecidableEq, Repr

namespace HalfInteger

/-- Two half-integers equal iff numerators equal -/
@[ext] theorem ext (x y : HalfInteger) (h : x.numerator = y.numerator) : x = y := by
  cases x; cases y; congr

/-- Create from numerator (Rust line 86) -/
def new (n : ℤ) : HalfInteger := ⟨n⟩

/-- Create from integer (Rust line 101) -/
def ofInt (n : ℤ) : HalfInteger := ⟨2 * n⟩

/-- Convert to rational (Rust line 113) -/
def toRat (x : HalfInteger) : ℚ := x.numerator / 2

/-- Zero (Rust line 160) -/
def zero : HalfInteger := ⟨0⟩

/-- Addition (Rust line 173) -/
instance : Add HalfInteger where
  add x y := ⟨x.numerator + y.numerator⟩

/-- Negation (Rust line 197) -/
instance : Neg HalfInteger where
  neg x := ⟨-x.numerator⟩

/-- Subtraction (Rust line 181) -/
instance : Sub HalfInteger where
  sub x y := ⟨x.numerator - y.numerator⟩

/-! ### Two Essential Theorems (NO SORRY) -/

/-- Addition is commutative -/
theorem add_comm (x y : HalfInteger) : x + y = y + x := by
  apply ext
  show (x + y).numerator = (y + x).numerator
  show x.numerator + y.numerator = y.numerator + x.numerator
  ring

/-- Zero is left identity -/
theorem zero_add (x : HalfInteger) : zero + x = x := by
  apply ext
  show (zero + x).numerator = x.numerator
  show 0 + x.numerator = x.numerator
  ring

end HalfInteger

/-! ## Vector8: 8-dimensional vectors with half-integer coordinates

From Rust (lines 239-242):
```rust
pub struct Vector8 {
    coords: [HalfInteger; 8],
}
```
-/

structure Vector8 where
  /-- 8 half-integer coordinates -/
  coords : Fin 8 → HalfInteger
  deriving DecidableEq

namespace Vector8

/-- Two vectors equal iff all coordinates equal -/
@[ext] theorem ext (v w : Vector8) (h : ∀ i, v.coords i = w.coords i) : v = w := by
  cases v; cases w; congr; funext i; exact h i

/-- Zero vector (Rust line 253) -/
def zero : Vector8 := ⟨fun _ => HalfInteger.zero⟩

instance : Inhabited Vector8 := ⟨zero⟩

/-- Inner product: ⟨v, w⟩ = Σᵢ vᵢ·wᵢ (Rust line 273) -/
def innerProduct (v w : Vector8) : ℚ :=
  ∑ i : Fin 8, (v.coords i).toRat * (w.coords i).toRat

/-- Norm squared: ‖v‖² = ⟨v, v⟩ (Rust line 283) -/
def normSquared (v : Vector8) : ℚ := innerProduct v v

/-- Vector addition (Rust line 295) -/
instance : Add Vector8 where
  add v w := ⟨fun i => v.coords i + w.coords i⟩

/-- Vector negation (Rust line 330) -/
instance : Neg Vector8 where
  neg v := ⟨fun i => -(v.coords i)⟩

/-- Vector subtraction (Rust line 302) -/
instance : Sub Vector8 where
  sub v w := ⟨fun i => v.coords i - w.coords i⟩

/-! ### Two Essential Theorems (NO SORRY) -/

/-- Inner product is commutative -/
theorem innerProduct_comm (v w : Vector8) : innerProduct v w = innerProduct w v := by
  unfold innerProduct
  congr 1
  ext i
  ring

/-- Zero is left identity for addition -/
theorem zero_add (v : Vector8) : zero + v = v := by
  apply ext
  intro i
  exact HalfInteger.zero_add (v.coords i)

end Vector8
