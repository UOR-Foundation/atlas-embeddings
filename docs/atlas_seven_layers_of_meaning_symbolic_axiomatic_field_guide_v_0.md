# Atlas — Seven Layers of Meaning

_A symbolic/axiomatic field guide built on the Universal Language (7)._  
Version: v0.2

> **Reading principle.** Each layer distills a working truth (proved below) that the next layer **adopts as an axiom**. Symbols and numbers are mnemonic, not mystical; they point to **form**.

---

## Layer 1 — Distinction (Mark)

**Glyphs:** `○` / `●` (empty/filled mark), bar `|`  
**Number:** **1** (and the latent **0**)  
**Axiom handed up:** _Distinctions are conserved by valid moves._

**Meaning.** A difference can be made and recognized. The world of Atlas begins when we can **mark** and **unmark** and detect sameness/otherness.

**Core moves.**

- `make` (introduce a mark), `erase` (remove a mark)
- `same?` / `diff?` tests (predicate of distinction)
- Duals exist: every move has a conceptual opposite

**Design cues.** Binary icons, contrast-only UI for the most primitive inspectors; think _black/white proofs_.

**Exercises.** Draw a 2×2 truth square for `same?/diff?` and note which transitions preserve the mark count.

---

## Layer 2 — Informational Action (Do/Undo)

**Glyphs:** arrow `→`, double arrow `↔`, pair `⟨do, undo⟩`  
**Number:** **2** (the dyad)  
**Axiom handed up:** \*Composition preserves a finite **resonance budget\***.

**Meaning.** Actions compose, and each action carries budgeted “conservation” (what our logic will call truth). Valid actions never create or destroy budget.

**Core moves.**

- `∘` composition; `id` identity
- `undo` witnesses reversibility (when present)
- Budget accounting: add, transfer, bound

**Design cues.** Always show an _energy/budget meter_ beside pipelines; failed steps debit budget and must be reconciled.

**Exercises.** Compose three actions and show that total budget before = after when all steps are valid.

---

## Layer 3 — Resonance Logic (Truth-as-Conservation)

**Glyphs:** balance ⚖︎ with **96** ticks; equivalence `≡`  
**Numbers:** **96** (resonance classes), **3** (admissible triple-checks)  
**Axiom handed up:** _Resonance-equivalence `≡₉₆` is the canonical sameness to be respected upstream._

**Meaning.** Statements are true to the extent they **conserve** resonance under all admissible actions. Two states are equivalent when they are budget-indistinguishable.

**Core moves.**

- Proof as _no-loss_ demonstration across generators
- Quotienting raw states by `≡₉₆`
- Budgets live in a semiring; tri-checks (compile–run–verify) are first-class

**Design cues.** Show truth as a conservation gauge; red/yellow/green becomes _less/matched/more_ conservation.

**Exercises.** Take a small state family and partition it into resonance classes by “survives all actions in G”.

---

## Layer 4 — Words of the Universal Language (7 Generators)

**Glyphs:** heptagram ✶; typed word `[α₁ α₂ … αₙ]`  
**Number:** **7** (minimal generative alphabet)  
**Axiom handed up:** _Well-typed words **encode to bytes**, and decoding respects `≡₉₆`._

**Meaning.** A compact, typed set of **seven** generators is enough to construct any computation/proof we need in Atlas while preserving resonance-equivalence.

**Core moves.**

- The seven families `α₁…α₇` (think: **mark**, **copy**, **swap**, **merge**, **split**, **quote**, **evaluate**)
- Typing rules enforce budget safety
- Normal forms exist for words up to `≡₉₆`

**Design cues.** Use seven distinct, texture-coded icons for the generators; tooltips show typing side-conditions.

**Exercises.** Factor a short word into a normal form using only local rewrites, then verify it leaves class membership unchanged.

---

## Layer 5 — Byte Lattice (256) and Resonance Quotient

**Glyphs:** 16×16 byte mandala; class coloring (maps 256 → 96)  
**Numbers:** **256** (state space), **96** (quotient classes)  
**Axiom handed up:** _There exists a **page decomposition** compatible with the classes._

**Meaning.** The concrete 8‑bit space `F₂⁸` is organized by resonance into **96** natural classes that guide coding, compression, and routing. The language lands here as encodings.

**Core moves.**

- Encode words → bytes; decode bytes → class representatives
- Masks and palettes on nibbles (16) as local structure
- Neighborhoods: adjacency by small-budget transitions

**Design cues.** A 16×16 grid UI with hover reveals: byte, class, legal moves, and nearest neighbors.

**Exercises.** Color the byte grid by `≡₉₆` and prove two different encodings land in the same class.

---

## Layer 6 — Page Calculus (λ = 48) and Tri‑Pass (×3 → 768)

**Glyphs:** 48‑petal rosette (scheduler), triskelion (triple pass)  
**Numbers:** **48** (page), **3** (passes), **768** (full tri‑cycle)  
**Axiom handed up:** _Boundary indices are **sufficient statistics** for reconstructing bulk state._

**Meaning.** Work is scheduled on a natural **48‑step** cycle; three passes (compile–run–verify) sweep the space coherently. The page layout respects byte‑class structure and makes audits natural.

**Core moves.**

- Page stepper, checkpointing, and repair
- Pass choreography: `P₁` prepare, `P₂` execute, `P₃` reconcile
- Error locality: defects pin to stable page facets

**Design cues.** Visualize processing as a rosette dial with three orbiting markers; logs align to page indices.

**Exercises.** Show that a defect introduced in `P₂` is detectable and repairable by the close of `P₃` on the same λ.

---

## Layer 7 — Boundary Belt and Regions (Content‑Addressed Atlas)

**Glyphs:** torus weave (48 × 256 = **12,288**), interlocking rings (regions)  
**Numbers:** **12,288** (belt), **∞** (open atlas of regions)  
**Axiom (closure back to L1):** _Validity = conservation of distinction across the whole stack._

**Meaning.** The boundary **encodes** the bulk: addresses and storage are boundary‑native, **content‑addressed** (placed by _what_ they are). Regions arise via **homomorphic resonance‑factorization**; programs are proofs executed over regions.

**Core moves.**

- Put/get by content; O(1) lookup/routing at the belt
- Region calculus: union, factor, quotient by homomorphism
- Polytope view: bulk recovered from the belt (holography)

**Design cues.** Navigation is a belt map with zooms into regions; search is phrased as “show me the class/region with X”.

**Exercises.** Demonstrate boundary reconstruction of a small bulk from belt samples; prove that two different build paths collide at the same content‑address.

---

# Cross‑walks & Mnemonics

**Number Rosetta.** 7 (alphabet) · 16 (nibble) · 48 (page) · 96 (classes) · 256 (byte) · 768 (tri‑cycle) · 12,288 (belt).  
**Shape Rosetta.** Dot/Mark · Arrow · Scale · Heptagram · 16×16 Grid · 48‑Rosette · Torus Weave.

**Cultural echoes (light touch).**  
Tri‑pass ↔ triple purification/verification rites; 16×16 grids ↔ mandalas/tables; boundary belt ↔ “as above, so below” motifs; heptagram ↔ generative alphabets.

---

# How to _use_ the ladder (practically)

1. **Teach** bottom‑up: prove a layer, _adopt_ it above.
2. **Design** top‑down: choose a region and descend until you hit concrete page/byte decisions.
3. **Debug** middle‑out: pin defects to λ, then to byte‑class, then rewrite the word causing the budget leak.

---

## Quick Reference (one‑liners)

- **L1 Distinction:** A difference can be made; valid moves conserve it.
- **L2 Action:** Actions compose; budget is conserved.
- **L3 Resonance:** Truth = conservation; sameness = `≡₉₆`.
- **L4 Words (7):** Typed words encode↔decode respecting `≡₉₆`.
- **L5 Byte→Class:** 256 states collapse to 96 classes; neighbors are budget‑local.
- **L6 Page (48):** Tri‑pass over pages gives global audit/repair.
- **L7 Belt & Regions:** Content‑addressed boundary reconstructs bulk; regions via homomorphic factorization.

---

---

# Seven Generator Icons (SVG)

Minimal, stroke‑based, monochrome icons sized 24×24. Names match the seven generative families we’ve been using.

**Mark** (`icon_mark.svg`)

```svg
<svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
  <circle cx="12" cy="12" r="8" />
  <circle cx="12" cy="12" r="2" fill="currentColor" stroke="none" />
</svg>
```

**Copy** (`icon_copy.svg`)

```svg
<svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
  <rect x="7" y="7" width="10" height="10" rx="1" />
  <rect x="4" y="4" width="10" height="10" rx="1" />
</svg>
```

**Swap** (`icon_swap.svg`)

```svg
<svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
  <path d="M4 9c2-4 14-4 16 0" />
  <polyline points="18,5 20,9 16,9" />
  <path d="M20 15c-2 4-14 4-16 0" />
  <polyline points="8,19 4,15 8,15" />
</svg>
```

**Merge** (`icon_merge.svg`)

```svg
<svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
  <circle cx="12" cy="12" r="2" />
  <path d="M4 6 L10 10" />
  <path d="M20 6 L14 10" />
  <path d="M12 14 L12 20" />
</svg>
```

**Split** (`icon_split.svg`)

```svg
<svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
  <circle cx="12" cy="10" r="2" />
  <path d="M12 12 L6 18" />
  <path d="M12 12 L18 18" />
  <path d="M12 4 L12 8" />
</svg>
```

**Quote** (`icon_quote.svg`)

```svg
<svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
  <polyline points="9,7 5,12 9,17" />
  <polyline points="15,7 19,12 15,17" />
</svg>
```

**Evaluate** (`icon_evaluate.svg`)

```svg
<svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
  <rect x="5" y="4" width="14" height="16" rx="2" />
  <polyline points="8,13 11,16 16,10" />
</svg>
```

**Downloadable set:** icon files were generated alongside this doc for convenience: `icon_mark.svg`, `icon_copy.svg`, `icon_swap.svg`, `icon_merge.svg`, `icon_split.svg`, `icon_quote.svg`, `icon_evaluate.svg`.

---

# Rosette Dial Widget Spec (λ = 48, tri‑pass)

**Purpose.** Visual scheduler and audit dial showing page index (0…47), tri‑pass progress, and budget health.

## Geometry

- Outer ring: 48 tick marks (λ facets) with numeric labels 0…47.
- Middle ring: tri‑pass orbit (3 markers for compile, run, verify).
- Inner hub: budget gauge (conservation meter).

## Data model

```ts
export type PassPhase = 'compile' | 'run' | 'verify';
export interface RosetteState {
  page: number; // 0..47
  phase: PassPhase; // current pass
  progress: number; // 0..1 within the phase
  budget: number; // 0..1 conservation health
  alerts?: { page: number; severity: 'info' | 'warn' | 'error'; msg: string }[];
}
```

## Component API (React/TS)

```tsx
<RosetteDial
  state={state}
  onPageChange={(p) => {}}
  onPhaseChange={(ph) => {}}
  onTick={(p) => {}}
  className="w-72 h-72"
/>
```

## Interaction

- Click on tick → set `page`.
- Keyboard: ←/→ step page; space cycles phase.
- Tooltips on ticks show page logs/defects.

## Rendering notes

- 48 ticks at angle `θ = 2π*i/48`.
- Phase markers orbit at `θ + 2π*progress/3` with distinct glyphs.
- Budget gauge maps to inner circle radius/opacity.

## Accessibility

- ARIA: `role="slider"` with `aria-valuemin="0" aria-valuemax="47" aria-valuenow={page}`.
- Live region announces phase transitions and alerts.

## Styling tokens

- `--dial-fg`, `--dial-bg`, `--dial-alert-warn`, `--dial-alert-error`.

## Optional: production-ready React skeleton

```tsx
import React from 'react';
export default function RosetteDial({
  state,
  onPageChange,
  onPhaseChange,
  onTick,
  className,
}: any) {
  const size = 320;
  const cx = size / 2,
    cy = size / 2,
    r = 140;
  const ticks = Array.from({ length: 48 }, (_, i) => {
    const a = -Math.PI / 2 + (2 * Math.PI * i) / 48;
    const x1 = cx + (r - 8) * Math.cos(a);
    const y1 = cy + (r - 8) * Math.sin(a);
    const x2 = cx + r * Math.cos(a);
    const y2 = cy + r * Math.sin(a);
    return (
      <g key={i} onClick={() => onPageChange?.(i)}>
        <line x1={x1} y1={y1} x2={x2} y2={y2} stroke="currentColor" />
        <text
          x={cx + (r + 14) * Math.cos(a)}
          y={cy + (r + 14) * Math.sin(a)}
          fontSize={9}
          textAnchor="middle"
          dominantBaseline="middle"
        >
          {i}
        </text>
      </g>
    );
  });
  return (
    <svg className={className} viewBox={`0 0 ${size} ${size}`}>
      <circle cx={cx} cy={cy} r={r} fill="none" stroke="currentColor" />
      {ticks}
      {/* phase marker */}
      <circle
        cx={cx + (r - 24) * Math.cos(-Math.PI / 2 + 2 * Math.PI * (state.page / 48))}
        cy={cy + (r - 24) * Math.sin(-Math.PI / 2 + 2 * Math.PI * (state.page / 48))}
        r={4}
      />
      {/* budget gauge */}
      <circle
        cx={cx}
        cy={cy}
        r={24 + 24 * state.budget}
        fill="currentColor"
        opacity={0.08 + 0.32 * state.budget}
      />
    </svg>
  );
}
```

---

# Byte‑Mandala Poster (16×16, colored by ≡₉₆) with Page Overlays

**What you get.** A print‑ready SVG poster that renders a 16×16 byte grid (00…FF), colored by resonance class (≡₉₆), plus an outer λ=48 rosette ring for page orientation and tri‑pass context.

**Status.** Updated to the **authoritative ≡₉₆ mapping** (no placeholders). Class index formula: `class = h2*24 + di*8 + low3`, with `h2=(b7 b6)∈{0..3}`, `di` from `(b4,b5)∈{00→0, 10→1, 01→2}`, `low3=(b3 b2 b1)∈{0..7}`. Canonical representatives fix `b0=0` and map `di={0,1,2}` to `(b4,b5)={00,10,01}` respectively.

**How to replace the mapping.**

- Find `class_from_byte(b)` in the SVG generator and substitute a 256‑entry lookup (0..95).
- Palette has 96 distinct hues; keep indices stable so the legend matches.

**Design details.**

- Grid: 16×16 cells, each labeled with its hex byte (`00`..`FF`).
- Color: 96‑hue wrap; stroke borders for print clarity.
- Overlays: outer λ=48 rosette with tick labels; dashed inner ring for tri‑pass alignment.
- Legend: 96 swatches with numeric class labels.
- Title block: includes a reminder about the placeholder mapping.

**Export.** Save/print at 300 DPI. The SVG is vector and scales cleanly.

**Download:** See links in the chat to grab the generated files.

---

---

# Atlas Symbol Grammar (new)

A compact construction system tying symbols to the authoritative ≡₉₆ structure.

## Primitives

- **Stroke:** 2px, rounded caps/joins.
- **Circle (C)**, **Line (L)**, **Polygon (P)**, **Text (T)**.
- **Angles:** 0°=east; 90°=south; 180°=west; −90°=north (clockwise positive).

## Layer Sigils (L1..L7)

- **L1 Distinction:** Ring with central dot.
- **L2 Action:** Two counter‑curved arrows (do/undo).
- **L3 Resonance:** Outer ring + three internal arcs (tri‑check).
- **L4 Words(7):** Heptagram {7/2}.
- **L5 Byte:** 4×4 mini‑grid.
- **L6 Page(48):** Rosette with 48 ticks.
- **L7 Belt:** Concentric torus (solid + dashed inner ring).

## Class Sigils (c00..c95)

- **h₂ (b7b6):** cardinal notch on the outer ring → N,E,S,W for {0,1,2,3}.
- **d₄₅ (from b4,b5):** center mark → dot (0), ▲ clockwise (1), ▲ counter‑clockwise (2).
- **low₃ (b3b2b1):** filled position on an 8‑dot inner ring.

This grammar yields a unique, human‑legible symbol for every ≡₉₆ class and composes cleanly with layer sigils.

---

# Assets (generated)

- **Layer Sigils sheet:** `atlas_layer_symbols.svg`
- **Class Sigils poster (96):** `class_sigil_poster.svg`
- **Sprite sheet (symbols & classes):** `atlas_symbol_sprite.svg`

Use the sprite `<symbol>` IDs `atlas_layer_1..7` and `atlas_class_c00..c95` in your SVG/React code via `<use xlink:href="#atlas_class_c42"/>` etc.
