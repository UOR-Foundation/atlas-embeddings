# Lean 4 Formalization Plan: Structural (Non-Computational) Proofs

**Status:** Requires major refactor
**Policy:** Proofs must be structural (no exhaustive enumeration)
**Goal:** Replace computational certificates with canonical Lean proofs grounded in mathlib

---

## Core Principles

1. **No enumeration-driven proofs.** Avoid `decide`, `native_decide`, and exhaustive `fin_cases` over large finite sets.
2. **Use mathlib structures.** Prefer `Module`, `InnerProductSpace`, `RootSystem`, `SimpleGraph`, and `CategoryTheory` definitions over bespoke structures.
3. **Separate data from proofs.** Implement definitions in one layer and prove general lemmas in a dedicated lemma library.
4. **Proofs follow mathematics, not code.** Rust computations are only hints for definitions, not proof strategies.

---

## Phase 0: Audit & Refactor Strategy

**Goal:** Establish boundaries between existing computational content and new structural content.

**Actions:**
- Identify every proof that relies on `native_decide`, `decide`, `fin_cases` for global verification.
- Isolate computational data (e.g., concrete root tables) behind a `Data` namespace so it can be phased out.
- Introduce a new namespace (e.g., `AtlasEmbeddings.Structural`) that houses the reworked proofs.

**Deliverables:**
- A refactor map showing which theorems are replaced by structural proofs.
- A temporary compatibility layer so existing modules compile while the rewrite proceeds.

---

## Phase 1: Algebraic & Lattice Foundations

**Goal:** Build the mathematical environment required for structural proofs.

### 1.1 Base Fields and Vector Spaces
- Choose a base field (`ℚ` or `ℝ`) for all analytic definitions.
- Define `V := (Fin 8 → ℚ)` with the standard inner product using `InnerProductSpace`.

### 1.2 Half-Integer Lattice
- Define the half-integer lattice as a subtype:
  - `HalfInt := {x : ℚ | x + x ∈ ℤ}` or an explicit `Subtype` of `ℚ` with denominator 2.
- Provide coercions and lemmas for arithmetic closure, parity, and norm calculations.

### 1.3 E₈ Lattice Definition
- Define `E8Lattice` as a `ℤ`-submodule of `V` using the classical parity condition:
  - either all coordinates are integers with even sum, or all are half-integers with odd sum.
- Prove closure under addition and negation.
- Prove integrality of inner products on the lattice.

**Success criteria:**
- All lattice operations and lemmas are proved without enumeration.
- The lattice is formally a `Submodule ℤ V` with proven parity invariants.

---

## Phase 2: E₈ Root System via Structure

**Goal:** Define the E₈ root system as a root system in `V` and prove its properties structurally.

### 2.1 Root Set Definition
- Define the set of roots as:
  - `Roots := {x ∈ E8Lattice | ⟪x, x⟫ = 2}`.
- Show `Roots` is closed under negation.

### 2.2 Root System Axioms
- Use mathlib’s `RootSystem` (or define a local structure matching it) and prove:
  - Root reflections preserve `Roots`.
  - The set spans `V`.

### 2.3 Simple Roots and Cartan Matrix
- Define simple roots using the standard E₈ basis (Dynkin diagram).
- Prove the Cartan matrix relations structurally using inner-product lemmas.
- Derive the root system classification (E₈ type) from the Cartan matrix.

### 2.4 Root Count (240) Without Enumeration
- Use the classification theorem for irreducible crystallographic root systems:
  - If the system is type E₈, then `#Roots = 240`.
- If mathlib does not yet supply this theorem, prove it from existing root system theory (Weyl group order + exponents).

**Success criteria:**
- E₈ root system defined as a `RootSystem` in Lean.
- Root count and norm properties derived structurally (no list enumeration).

---

## Phase 3: Atlas as a Structural Graph

**Goal:** Define the Atlas graph in mathlib’s graph framework and prove properties structurally.

### 3.1 Graph Definition
- Use `SimpleGraph` with vertex type `AtlasLabel` or an abstract type of resonance classes.
- Define adjacency via the unity constraint or an equivalent algebraic relation.

### 3.2 Mirror Symmetry
- Define the involution `τ` on vertices.
- Prove `τ` is an automorphism of the graph (structure-preserving) using algebraic properties.

### 3.3 Degree and Orbit Structure
- Prove degree distribution using symmetry/orbit arguments (automorphism group action), not enumeration.

**Success criteria:**
- Atlas graph is defined as a `SimpleGraph` with proven symmetry and degree lemmas.

---

## Phase 4: Atlas → E₈ Embedding (Structural)

**Goal:** Define and prove the embedding using lattice and parity arguments.

### 4.1 Map Definition
- Define the embedding as a function `AtlasLabel → E8Lattice` via coordinate extension.
- Prove it lands in `Roots` using parity and norm calculations.

### 4.2 Injectivity
- Prove injectivity via algebraic inversion: the 6-tuple is recoverable from the 8-tuple under parity constraints.

### 4.3 Adjacency Preservation
- Prove adjacency preservation using inner products and the unity constraint relation.

**Success criteria:**
- Embedding is a graph homomorphism into the E₈ root graph with structural proofs.

---

## Phase 5: Category-Theoretic Framework

**Goal:** Build the categorical machinery using mathlib’s `CategoryTheory`.

### 5.1 The Category ResGraph
- Define objects as resonance graphs with suitable structure.
- Define morphisms as adjacency-preserving maps.
- Use `CategoryTheory` to give a canonical category instance.

### 5.2 Categorical Operations
- Define product, quotient, filtration, and augmentation as categorical constructions.
- Prove universal properties structurally (not by vertex enumeration).

### 5.3 Initiality of Atlas
- Prove Atlas is initial via universal properties and uniqueness of morphisms.

**Success criteria:**
- Atlas initiality proven in the categorical sense with standard categorical proofs.

---

## Phase 6: Exceptional Groups via Root Systems

**Goal:** Define G₂, F₄, E₆, E₇, E₈ as root systems and relate them to the categorical constructions.

- Use mathlib’s root system definitions for each type.
- Prove equivalences between categorical constructions and root-system definitions.
- Derive root counts and ranks from root system theorems.

**Success criteria:**
- Each exceptional group is characterized by a root system isomorphism, not a finite lookup.

---

## Phase 7: Completeness (No Sixth Group)

**Goal:** Prove classification results that only five exceptional types exist.

- Use classification theorems for irreducible crystallographic root systems.
- Formalize that the only exceptional Dynkin diagrams are G₂, F₄, E₆, E₇, E₈.

**Success criteria:**
- The completeness theorem is a consequence of root system classification, not enumeration.

---

## Phase 8: Proof Infrastructure and Refactoring

**Goal:** Replace computational proofs with structural proofs throughout the codebase.

**Actions:**
- Introduce lemma libraries for parity, lattice arithmetic, and graph morphisms.
- Replace existing `native_decide` theorems with formal lemmas.
- Maintain compatibility while migrating modules.

---

## Deliverables Checklist

- [ ] `E8Lattice` defined as a `Submodule` with parity invariants
- [ ] `RootSystem` instance for E₈ with simple roots and Cartan matrix
- [ ] Atlas graph defined as `SimpleGraph` with symmetry lemmas
- [ ] Structural embedding proof into E₈
- [ ] Category-theoretic proofs using universal properties
- [ ] Root-system characterizations for G₂–E₈
- [ ] Classification-based completeness theorem

---

## Non-Computational Proof Policy

**Forbidden proof styles:**
- Exhaustive case splits over 96 or 240 elements
- `native_decide` or `decide` to establish global properties
- Proofs that mirror Rust enumeration logic

**Required proof styles:**
- Lemmas derived from algebraic structure
- Root system and Weyl group theory
- Category-theoretic universal properties
- Structural arguments using mathlib abstractions

---

**End of Plan**
