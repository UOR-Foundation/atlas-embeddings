/-
Copyright (c) 2025 Atlas Embeddings Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sanity Tests for Heisenberg Group

Basic sanity checks to verify the Heisenberg group formalization is working correctly.
These are simple, decidable properties that can be checked automatically.
-/

import Math.Heisenberg.Core
import Math.Pauli.Commutator
import Mathlib.Data.ZMod.Basic

namespace SanityTests

open HeisenbergElem Pauli

/-! ## Basic Group Properties -/

/-- Test: identity multiplication -/
example : (one : HeisenbergElem 2) * one = one := by rfl

/-- Test: center element structure -/
example : (center 0 : HeisenbergElem 2).v = (fun _ => 0, fun _ => 0) := by rfl

/-- Test: center multiplication -/
example : (center 1 : HeisenbergElem 2) * center 1 = center 0 := by
  simp [center, mul, symplecticForm]
  ext
  · simp [ZMod.add_self_eq_zero]
  · ext i; rfl
  · ext i; rfl

/-! ## Symplectic Form Tests -/

/-- Test: ω is alternating -/
example : ω 2 ((fun _ => 1, fun _ => 0) : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2))
                ((fun _ => 1, fun _ => 0) : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) = 0 := by
  simp [symplecticForm]
  decide

/-- Test: ω detects X-Z anticommutation -/
example : ω 2 ((fun i => if i = 0 then 1 else 0, fun _ => 0) : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2))
                ((fun _ => 0, fun i => if i = 0 then 1 else 0) : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) = 1 := by
  simp [symplecticForm]
  decide

/-! ## Pauli Commutation Tests -/

/-- Test: X₀² = 1 -/
example : X_basis (0 : Fin 2) * X_basis 0 = one := by
  exact X_sq 0

/-- Test: Z₀² = 1 -/
example : Z_basis (0 : Fin 2) * Z_basis 0 = one := by
  exact Z_sq 0

/-- Test: X₀ and X₁ commute -/
example : X_basis (0 : Fin 2) * X_basis 1 = X_basis 1 * X_basis 0 := by
  exact X_X_commute 0 1

/-- Test: Z₀ and Z₁ commute -/
example : Z_basis (0 : Fin 2) * Z_basis 1 = Z_basis 1 * Z_basis 0 := by
  exact Z_Z_commute 0 1

/-! ## Commutator Tests -/

/-- Test: [X₀, Z₀] is central -/
example : (commutator (X_basis (0 : Fin 2)) (Z_basis 0)).v = (fun _ => 0, fun _ => 0) := by
  have := X_Z_same_anticommute (0 : Fin 2)
  rw [this]
  rfl

/-- Test: [X₀, Z₀] = center(1) = -I -/
example : commutator (X_basis (0 : Fin 2)) (Z_basis 0) = center 1 := by
  exact X_Z_same_anticommute 0

/-! ## Explicit n=1 Tests -/

/-- For n=1, test all 4 elements of (F₂)² -/
example (s₁ s₂ : ZMod 2) :
    let v₁ := ((fun _ : Fin 1 => s₁), (fun _ : Fin 1 => 0))
    let v₂ := ((fun _ : Fin 1 => s₂), (fun _ : Fin 1 => 0))
    ω 1 v₁ v₂ = 0 := by
  simp [symplecticForm]
  decide

/-! ## Inverse Tests -/

/-- Test: inverse cancels -/
example (x z : Fin 2 → ZMod 2) :
    let h := ⟨(0 : ZMod 2), (x, z)⟩
    h * h⁻¹ = (one : HeisenbergElem 2) := by
  exact mul_inv _

/-- Test: self-inverse in characteristic 2 -/
example (x z : Fin 2 → ZMod 2) :
    let h : HeisenbergElem 2 := ⟨0, (x, z)⟩
    h⁻¹ = h := by rfl

/-! ## Vector Addition Tests -/

/-- Test: vector components add coordinatewise -/
example :
    let h₁ : HeisenbergElem 2 := ⟨0, (fun i => if i = 0 then 1 else 0, fun _ => 0)⟩
    let h₂ : HeisenbergElem 2 := ⟨0, (fun i => if i = 1 then 1 else 0, fun _ => 0)⟩
    (h₁ * h₂).v = (fun i => 1, fun _ => 0) := by
  simp [mul, symplecticForm]
  ext
  · ext i
    fin_cases i <;> decide
  · ext i; rfl

/-! ## Concrete Multiplication Examples -/

/-- Test: specific multiplication -/
example :
    let h₁ : HeisenbergElem 1 := ⟨0, (fun _ => 1, fun _ => 0)⟩  -- X
    let h₂ : HeisenbergElem 1 := ⟨0, (fun _ => 0, fun _ => 1)⟩  -- Z
    let prod := h₁ * h₂
    prod.s = 1 ∧ prod.v = (fun _ => 1, fun _ => 1) := by
  simp [mul, symplecticForm]
  constructor
  · decide
  · ext
    · ext i; rfl
    · ext i; rfl

end SanityTests
