# Atlas Sigil Algebra — Formal Specification (v1.0)

> **Scope.** This document formalizes the operational semantics, algebra, and executable grammar for Atlas sigils, aligning them with the 7‑generator Universal Language and the authoritative ≡₉₆ class structure.

---

## 0. Preliminaries

- Let **B** = {0,1} and let bytes be elements of B⁸ with bit order `(b7 b6 b5 b4 b3 b2 b1 b0)`.
- The **authoritative class index** function `class_index : B⁸ → {0..95}` is:
  - `h₂ = (b7<<1) | b6 ∈ {0..3}`
  - `d₄₅ = 0 if (b4,b5)=(0,0); 1 if (1,0); 2 if (0,1)`
  - `low₃ = (b3<<2)|(b2<<1)|b1 ∈ {0..7}`
  - **Class:** `C(b) = 24*h₂ + 8*d₄₅ + low₃`.
- **Canonical representative** `rep : {0..95} → B⁸` fixes `b0=0` and chooses `(b4,b5)` by `d₄₅∈{0,1,2}↦{00,10,01}` (and inverts `h₂, low₃` accordingly).

We write **≡₉₆** for equality of class index: `x ≡₉₆ y ⇔ C(x)=C(y)`.

---

## 1. Sigil Syntax (Abstract)

A **class‑sigil** is the triple `σ = (h₂, d, ℓ)` with `h₂∈{0..3}, d∈{0,1,2}, ℓ∈{0..7}`.

A **layer‑sigil** is one of `{Distinction, Action, Resonance, Words, Byte, Page, Belt}` used as an operator tag (see §5).

The **visual** form encodes `(h₂,d,ℓ)` as _(cardinal notch, center marker, inner 8‑dot ring)_.

---

## 2. Algebra of Combination

Let **Σ** be the set of all sigils (layer or class). We equip Σ with:

### 2.1 Sequential Composition

Operator `∘ : Σ×Σ → Σ` on **typed terms** (see §5). Reading: _first s₁, then s₂_.

- **Associativity:** `(s₃∘s₂)∘s₁ = s₃∘(s₂∘s₁)` (when types match).
- **Unit:** `ε` (empty action). `s∘ε = ε∘s = s`.

### 2.2 Parallel Superposition

Operator `⊗ : Σ×Σ → Σ` (symmetric monoidal product).

- **Commutative:** `s₁⊗s₂ = s₂⊗s₁`.
- **Associative:** `(s₁⊗s₂)⊗s₃ = s₁⊗(s₂⊗s₃)`.
- **Unit:** `⊙` (transparent/identity wire). `s⊗⊙=s`.

### 2.3 Transformations (Scope/Context Actions)

- **Quarter‑turn** `R : Σ→Σ`, `R(h₂,d,ℓ) = ((h₂+1) mod 4, d, ℓ)`.
- **Inner‑twist** `T_k : Σ→Σ`, `T_k(h₂,d,ℓ) = (h₂, d, (ℓ+k) mod 8)`.
- **Mirror** `M : Σ→Σ`, flips modality `d: 1↔2`, preserves `0`; reflects `h₂` about a chosen axis and accordingly maps the 8‑ring index `ℓ`.

> **Axiom (Equivariance).** `R, T_k, M` act by **class permutations** and therefore preserve ≡₉₆ and resonance budgets.

---

## 3. Static Semantics (Types & Budgets)

- There is a budget semiring `(𝔹, ⊕, ⊗, 0, 1)` capturing **resonance conservation**.
- Each generator (see §5.1) has a _typing judgement_ `Γ ⊢ op : A → B ▷ β`, where `β∈𝔹` is the **budget profile**.
- **Sequential rule:**
  - If `Γ ⊢ s₁ : A→B ▷ β₁` and `Γ ⊢ s₂ : B→C ▷ β₂` then `Γ ⊢ s₂∘s₁ : A→C ▷ β₂⊗β₁`.
- **Parallel rule:**
  - If `Γ ⊢ s₁ : A₁→B₁ ▷ β₁` and `Γ ⊢ s₂ : A₂→B₂ ▷ β₂` then `Γ ⊢ s₁⊗s₂ : A₁×A₂→B₁×B₂ ▷ β₁⊕β₂`.
- **Conservation law:** All well‑typed closed terms satisfy **no‑loss**: the realized trace respects the global budget invariant from Resonance Logic.

---

## 4. Denotational Semantics

Two interoperable interpretations:

### 4.1 Literal (Byte) Semantics

- Map `⟦·⟧_B : (class‑sigils)* → B⁸*` by `⟦c_i⟧_B = rep(i)` and concatenation on sequences.
- With an optional page index `λ∈{0..47}`, define **belt addresses** `addr(λ, b) = 256·λ + b ∈ {0..12287}`.

### 4.2 Operational (Word) Semantics

- Fix the seven generators `G = {mark, copy, swap, merge, split, quote, evaluate}`.
- A **sigil‑parameterized operator** is written `g@σ` where `σ=(h₂,d,ℓ)`.
- Lowering function `⟦·⟧_G : Terms → Words(G)` satisfies:
  - `⟦g@σ⟧_G = core_g ⟨h₂,d,ℓ⟩` (a well‑typed word that consults the triple for direction/phase/context).
  - `⟦s₂∘s₁⟧_G = ⟦s₂⟧_G · ⟦s₁⟧_G`, `⟦s₁⊗s₂⟧_G = ⟦s₁⟧_G ⊗ ⟦s₂⟧_G`.
  - `⟦R(s)⟧_G = ρ · ⟦s⟧_G · ρ^{-1}`; similarly for `T_k, M` via dedicated control words.

> **Soundness.** If `t` is well‑typed then evaluation of `⟦t⟧_G` preserves budgets and respects ≡₉₆.

---

## 5. Generators and Modality Table

### 5.1 Generators (operational roles)

- `mark` — introduce/remove a mark (creation in neutral mode guarded by budget).
- `copy` — comultiplication (fan‑out); biased by `d`.
- `swap` — symmetry/braid on wires.
- `merge` — fold/meet; `d=1` (produce) vs `d=2` (consume) select monoid flavor.
- `split` — case analysis/deconstruct by context `ℓ`.
- `quote` — suspend; binds to context `ℓ`.
- `evaluate` — force/thunk discharge; consults scope `h₂`.

### 5.2 Modalities (center marker)

- `d=0` • neutral/conservative
- `d=1` ▲ clockwise → **produce / write / forward**
- `d=2` ▲ counter‑clockwise → **consume / read / backward**

### 5.3 Scope (cardinal notch) & Context (8‑ring)

- `h₂∈{0,1,2,3}` bind operations to quadrants (e.g., Compile, Run, Verify, I/O).
- `ℓ∈{0..7}` selects a binding slot, local state, or 8‑phase tick.

---

## 6. Transform Calculus

- **Normalization:** any composite `R^a T_k M^m (s₁ ⊗ ··· ⊗ s_n)` can be rewritten by _pushing transforms inside_ until only atomic sigils carry `(h₂,d,ℓ)` updates. This yields a canonical form.
- **Distribution laws:**
  - `R(s₂∘s₁)=R(s₂)∘R(s₁)`, `R(s₁⊗s₂)=R(s₁)⊗R(s₂)`; similarly for `T_k, M`.
- **Invariants:** `C(rep(C(s)))` is fixed; transforms act as permutations on class indices.

---

## 7. Executable Surface Grammar (EBNF)

```
<sigil>      ::= "c" <00..95> ["^" ("+"|"-") <k:int>] ["~"] ["@" <λ:int>]
<op>         ::= ("mark"|"copy"|"swap"|"merge"|"split"|"quote"|"evaluate") "@" <sigil>
<term>       ::= <op> | "(" <term> ")"
<seq>        ::= <term> { "." <term> }                // ∘
<par>        ::= <seq>  { "||" <seq> }                // ⊗
<transform>  ::= [ "R" ("+"|"-") <q:int> ] [ "T" ("+"|"-") <k:int> ] [ "~" ]
<phrase>     ::= [ <transform> "@" ] <par>
```

**Examples.**

- `c42^+3~@17` (class 42, inner‑twist +3, mirrored, on page λ=17)
- `evaluate@c21 . copy@c05 || swap@c72` (sequential then parallel)

---

## 8. Laws & Derived Combinators

- **Associativity/Commutativity/Units** as in §2.
- **Boolean macros** (fix a quadrant and two low₃ slots):
  - `NOT(x)  ≔  M ∘ T₄ @ x`
  - `AND(x,y) ≔ merge@c(consume) ∘ (x || y)`
  - `OR(x,y)  ≔ merge@c(produce) ∘ (x || y)`
- **Scoped op:** `scope(q, t) ≔ R^{q} ∘ t ∘ R^{-q}`.
- **Ring step:** `step(k, t) ≔ T_{k} ∘ t`.

---

## 9. Implementation Notes

- **Byte backend:** use `rep(class)` to emit bytes; include optional belt addressing `addr(λ, byte)`.
- **Word backend:** provide small library words `ρ, τ_k, μ` implementing `R, T_k, M`.
- **Canonicalization:** normalize transforms; stable pretty‑printer shows explicit `(h₂,d,ℓ)` per atomic op.
- **Sprites:** reference visual symbols via `atlas_layer_1..7` and `atlas_class_c00..c95` from the SVG sprite sheet.

---

## 10. Soundness & Safety (Sketch)

- **Soundness w.r.t. ≡₉₆:** `R, T_k, M` permute class indices; `⊗,∘` composition cannot cross classes except via typed homomorphisms, so resonance budgets are preserved.
- **Progress/Preservation:** typed programs either _step_ or are _values_; budgets are preserved modulo accounted work.
- **Determinism:** both literal and word interpreters are deterministic for closed programs.

---

## 11. Worked Examples

1. **Context marching:** `T₁∘T₁∘T₁` moves three steps on the 8‑ring (useful for an 8‑phase clock).
2. **Scoped split:** `R² ∘ split@cX ∘ R⁻²` applies a split only in the S quadrant, leaving outer scope intact.
3. **Function application:** `evaluate@cℓ ∘ (quote@cℓ ⊗ id)` forces a quoted value bound at slot ℓ.

---

**End of v1.0**
