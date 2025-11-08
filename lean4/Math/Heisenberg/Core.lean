/-
Copyright (c) 2025 Atlas Embeddings Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Heisenberg Group Core Structure

This module formalizes the Heisenberg group H(n) over F₂ = ℤ/2ℤ
as a central extension of the symplectic vector space (F₂)^{2n}.

## Mathematical Structure

The Heisenberg group H(n) is defined by:
- Underlying set: F₂ × (F₂)^{2n}
- Multiplication via 2-cocycle: (s₁, v₁) · (s₂, v₂) = (s₁ + s₂ + ω(v₁, v₂), v₁ + v₂)
- Identity: (0, 0)
- Inverse: (s, v)⁻¹ = (s + ω(v, v), v) = (s, v) since ω(v, v) = 0

where ω: (F₂)^{2n} × (F₂)^{2n} → F₂ is the symplectic form.

## Key Properties

1. Central extension: 1 → F₂ → H(n) → (F₂)^{2n} → 1
2. Center: Z(H) = {(s, 0) : s ∈ F₂}
3. Commutator: [(s₁, v₁), (s₂, v₂)] = (ω(v₁, v₂), 0)
4. Exponent: 2 (every element has order dividing 2)
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.GroupTheory.GroupAction.Basic

/-! ## Symplectic Form on F₂^{2n} -/

/-- The symplectic form ω on (F₂)^{2n}, where vectors are represented as pairs (x, z) ∈ (F₂)^n × (F₂)^n. -/
def symplecticForm (n : ℕ) (v₁ v₂ : (Fin n → ZMod 2) × (Fin n → ZMod 2)) : ZMod 2 :=
  let (x₁, z₁) := v₁
  let (x₂, z₂) := v₂
  (Finset.sum Finset.univ fun i => x₁ i * z₂ i) - 
  (Finset.sum Finset.univ fun i => z₁ i * x₂ i)

notation "ω" => symplecticForm

/-- The symplectic form is alternating: ω(v, v) = 0 -/
theorem symplectic_alternating (n : ℕ) (v : (Fin n → ZMod 2) × (Fin n → ZMod 2)) :
    ω n v v = 0 := by
  obtain ⟨x, z⟩ := v
  simp [symplecticForm]
  ring

/-- The symplectic form is antisymmetric: ω(v₁, v₂) = -ω(v₂, v₁) = ω(v₂, v₁) in characteristic 2 -/
theorem symplectic_antisym (n : ℕ) (v₁ v₂ : (Fin n → ZMod 2) × (Fin n → ZMod 2)) :
    ω n v₁ v₂ = ω n v₂ v₁ := by
  obtain ⟨x₁, z₁⟩ := v₁
  obtain ⟨x₂, z₂⟩ := v₂
  simp [symplecticForm]
  ring

/-! ## Heisenberg Group Structure -/

/-- The Heisenberg group H(n) as a set: F₂ × (F₂)^{2n} -/
structure HeisenbergElem (n : ℕ) where
  /-- Central component (phase) -/
  s : ZMod 2
  /-- Vector component in (F₂)^{2n}, split as (x, z) -/
  v : (Fin n → ZMod 2) × (Fin n → ZMod 2)
  deriving DecidableEq

namespace HeisenbergElem

variable {n : ℕ}

/-- Identity element: (0, (0, 0)) -/
def one : HeisenbergElem n := ⟨0, (fun _ => 0, fun _ => 0)⟩

/-- Multiplication using the cocycle -/
def mul (h₁ h₂ : HeisenbergElem n) : HeisenbergElem n :=
  let (x₁, z₁) := h₁.v
  let (x₂, z₂) := h₂.v
  ⟨h₁.s + h₂.s + ω n h₁.v h₂.v, (fun i => x₁ i + x₂ i, fun i => z₁ i + z₂ i)⟩

/-- Inverse element -/
def inv (h : HeisenbergElem n) : HeisenbergElem n :=
  ⟨h.s, h.v⟩  -- In characteristic 2, v⁻¹ = v and s⁻¹ = s, ω(v,v) = 0

/-- Multiplication is associative -/
theorem mul_assoc (h₁ h₂ h₃ : HeisenbergElem n) :
    mul (mul h₁ h₂) h₃ = mul h₁ (mul h₂ h₃) := by
  simp [mul]
  obtain ⟨s₁, x₁, z₁⟩ := h₁
  obtain ⟨s₂, x₂, z₂⟩ := h₂
  obtain ⟨s₃, x₃, z₃⟩ := h₃
  ext
  · simp [symplecticForm]
    ring
  · ext i; ring
  · ext i; ring

/-- Left identity -/
theorem one_mul (h : HeisenbergElem n) : mul one h = h := by
  simp [mul, one]
  obtain ⟨s, x, z⟩ := h
  ext
  · simp [symplecticForm]
  · ext i; ring
  · ext i; ring

/-- Right identity -/
theorem mul_one (h : HeisenbergElem n) : mul h one = h := by
  simp [mul, one]
  obtain ⟨s, x, z⟩ := h
  ext
  · simp [symplecticForm]
  · ext i; ring
  · ext i; ring

/-- Left inverse -/
theorem inv_mul (h : HeisenbergElem n) : mul (inv h) h = one := by
  simp [mul, inv, one]
  obtain ⟨s, x, z⟩ := h
  ext
  · simp [symplectic_alternating]
  · ext i; simp [ZMod.add_self_eq_zero]
  · ext i; simp [ZMod.add_self_eq_zero]

/-- Right inverse -/
theorem mul_inv (h : HeisenbergElem n) : mul h (inv h) = one := by
  simp [mul, inv, one]
  obtain ⟨s, x, z⟩ := h
  ext
  · simp [symplecticForm, symplectic_alternating]
    ring
  · ext i; simp [ZMod.add_self_eq_zero]
  · ext i; simp [ZMod.add_self_eq_zero]

/-! ## Group Instance -/

instance : Group (HeisenbergElem n) where
  mul := mul
  one := one
  inv := inv
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  inv_mul_cancel := inv_mul

/-! ## Center Characterization -/

/-- The center element with phase s and zero vector -/
def center (s : ZMod 2) : HeisenbergElem n := ⟨s, (fun _ => 0, fun _ => 0)⟩

/-- An element is central iff its vector part is zero -/
theorem mem_center_iff (h : HeisenbergElem n) :
    h ∈ Set.center (Set.univ : Set (HeisenbergElem n)) ↔ 
    h.v = (fun _ => 0, fun _ => 0) := by
  constructor
  · intro hc
    by_contra hn
    -- If v ≠ 0, we can find an element that doesn't commute
    sorry  -- Requires finding a specific non-commuting element
  · intro hv
    intro g _
    obtain ⟨s, v⟩ := h
    rw [hv]
    simp [mul]
    obtain ⟨s', v'⟩ := g
    ext
    · simp [symplecticForm]
    · ext i; ring
    · ext i; ring

/-- The center consists exactly of {(0, 0), (1, 0)} -/
theorem center_eq_scalars :
    Set.center (Set.univ : Set (HeisenbergElem n)) = 
    {h : HeisenbergElem n | h.v = (fun _ => 0, fun _ => 0)} := by
  ext h
  exact mem_center_iff h

/-! ## Commutator Formula -/

/-- Commutator of two Heisenberg elements -/
def commutator (h₁ h₂ : HeisenbergElem n) : HeisenbergElem n :=
  h₁ * h₂ * h₁⁻¹ * h₂⁻¹

/-- The commutator is determined by the symplectic form -/
theorem commutator_eq_center (h₁ h₂ : HeisenbergElem n) :
    commutator h₁ h₂ = center (ω n h₁.v h₂.v) := by
  simp [commutator, mul, inv, center]
  obtain ⟨s₁, x₁, z₁⟩ := h₁
  obtain ⟨s₂, x₂, z₂⟩ := h₂
  ext
  · simp [symplecticForm, symplectic_alternating]
    ring
  · ext i; simp [ZMod.add_self_eq_zero]
  · ext i; simp [ZMod.add_self_eq_zero]

end HeisenbergElem

/-! ## Projection to Quotient -/

/-- Projection to the quotient (F₂)^{2n} -/
def projectToQuotient {n : ℕ} (h : HeisenbergElem n) : (Fin n → ZMod 2) × (Fin n → ZMod 2) :=
  h.v

/-- The projection is a group homomorphism to the abelian quotient -/
theorem project_mul {n : ℕ} (h₁ h₂ : HeisenbergElem n) :
    projectToQuotient (h₁ * h₂) = 
    let (x₁, z₁) := projectToQuotient h₁
    let (x₂, z₂) := projectToQuotient h₂
    (fun i => x₁ i + x₂ i, fun i => z₁ i + z₂ i) := by
  simp [projectToQuotient, HeisenbergElem.mul]
  obtain ⟨x₁, z₁⟩ := h₁.v
  obtain ⟨x₂, z₂⟩ := h₂.v
  rfl

/-! ## Representation Space (Axiomatized) -/

/-- The standard representation space of H(n) -/
axiom RepSpace (n : ℕ) : Type

/-- Action of H(n) on the representation space -/
axiom repAction (n : ℕ) : HeisenbergElem n → RepSpace n → RepSpace n

/-- Central elements act as scalars -/
axiom central_acts_as_scalar (n : ℕ) (s : ZMod 2) (ψ : RepSpace n) :
    repAction n (HeisenbergElem.center s) ψ = 
    (if s = 0 then ψ else sorry)  -- -ψ when s = 1 (phase -1)
