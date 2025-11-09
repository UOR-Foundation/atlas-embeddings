# Atlas Sigil Parser Spec + Test Vectors (with 2‑page Reference) · v1.0

> A minimal, executable specification for parsing, transforming, and evaluating **sigil phrases** in Atlas. Includes **literal (byte)** and **operational (word)** backends and a concise **two‑page reference** for print.

---

## 1) Surface Grammar (EBNF)

```
<sigil>      ::= "c" <int:0..95> ["^" ("+"|"-") <int>] ["~"] ["@" <λ:int 0..47>]
<op>         ::= ("mark"|"copy"|"swap"|"merge"|"split"|"quote"|"evaluate") "@" <sigil>
<term>       ::= <op> | "(" <term> ")"
<seq>        ::= <term> { "." <term> }                // ∘ sequential
<par>        ::= <seq>  { "||" <seq> }                // ⊗ parallel
<transform>  ::= [ "R" ("+"|"-") <q:int> ] [ "T" ("+"|"-") <k:int> ] [ "~" ]
<phrase>     ::= [ <transform> "@" ] <par>
```

**Notes.**

- Numbers in `cN` are **decimal** 0..95. `λ` is 0..47.
- Transform prefix `[transform@]` applies to the whole `<par>` (distributes inside).
- Postfix on a single sigil: `cN^+k~@λ` applies _after_ the prefix is distributed.

---

## 2) Lexical Conventions

- **Tokens:** `c`, integers, identifiers (the 7 ops), symbols `.^|()@||R T ~ + -`.
- **Whitespace/comments:** spaces and `// …` to end‑of‑line are ignored.
- **Precedence:** parentheses > `.` (∘) > `||` (⊗). Transform prefix binds tight to its following `<par>`.

---

## 3) Abstract Syntax Tree (AST)

```ts
// Core carriers
export type ClassSigil = {
  kind: 'Sigil';
  n: number;
  rotate?: number;
  mirror?: boolean;
  page?: number;
};
export type OpName = 'mark' | 'copy' | 'swap' | 'merge' | 'split' | 'quote' | 'evaluate';
export type Op = { kind: 'Op'; op: OpName; sigil: ClassSigil };

// Composition
export type Seq = { kind: 'Seq'; items: Term[] }; // s2∘s1∘...
export type Par = { kind: 'Par'; branches: Seq[] }; // s1 || s2 || ...

// Transforms acting on Terms
export type Transform = { R?: number; T?: number; M?: boolean };
export type Transformed = { kind: 'Xform'; x: Transform; body: Par };

export type Term = Op | { kind: 'Group'; body: Par };
export type Phrase = Transformed | Par;
```

**Normalization idea.** Push `R/T/M` into leaves so each `Sigil` carries the final `(h₂,d,ℓ)` (see §6).

---

## 4) Semantics of Sigils (authoritative mapping)

Let `ci∈{0..95}`. Decode:

- `h₂ = ci // 24 ∈ {0,1,2,3}`
- `d = (ci % 24) // 8 ∈ {0,1,2}` with `(b4,b5) ∈ {00,10,01}`
- `ℓ = ci % 8 ∈ {0..7}`
  **Transforms:**
- `R+q`: `h₂ := (h₂+q) mod 4`. `R-q` subtracts.
- `T+k`: `ℓ := (ℓ+k) mod 8`. `T-k` subtracts.
- `~` (mirror): `d: 1↔2`, `0→0`. (Axis‑specific `h₂,ℓ` reflections are optional extensions.)
  **Canonical byte (literal backend):** set `b0=0`; write bits from `(h₂,d,ℓ)` as in the formal spec; assemble to a byte `rep(ci')` where `ci' = 24*h₂ + 8*d + ℓ` _after transforms_.
  **Belt address:** if `page=λ` present, `addr = 256*λ + byte`.

---

## 5) Operational Backend (word lowering)

Each `op@σ` lowers to a word over the 7 generators parameterized by `σ=(h₂,d,ℓ)`.

```ts
// Sketch only — core_g returns a small word honoring modality/scope/context
function lowerOp(op: OpName, sigma: { h2: number; d: number; l: number }): string[] {
  switch (op) {
    case 'copy':
      return ['copy', mode(sigma.d), ctx(sigma.l)];
    case 'merge':
      return ['merge', mode(sigma.d)];
    case 'split':
      return ['split', ctx(sigma.l)];
    case 'quote':
      return ['quote', ctx(sigma.l)];
    case 'evaluate':
      return [phase(sigma.h2), 'evaluate']; // phase selects quadrant policy
    case 'swap':
      return ['swap'];
    case 'mark':
      return ['mark'];
  }
}
```

Composition: concatenate words for `.`; take monoidal product for `||`. Transforms insert control words (`ρ` for `R`, `τ_k` for `T`, `μ` for mirror) that commute to leaves and normalize away.

---

## 6) Parser Reference Implementation (TypeScript, no deps)

```ts
export function parsePhrase(src: string): Phrase {
  /* LL(1) hand‑parser: tokenize -> parsePar -> maybe prefix transform */
}
export function evalLiteral(p: Phrase): { bytes: number[]; addrs?: number[] } {
  /* normalize transforms; collect leaves; emit canonical bytes; addrs if page set */
}
export function evalOperational(p: Phrase): string[] {
  /* lower ops to words; return flat instruction list */
}
```

**Tokenizer (sketch).** Recognize `c`, decimal int, identifiers in {mark,copy,swap,merge,split,quote,evaluate}, symbols `.`, `||`, `(`, `)`, `@`, `^`, `~`, `R±q`, `T±k`.

---

## 7) Test Vectors (authoritative)

### 7.1 Literal (byte) mode

1. **Single sigil** — `c21`
   - Decode: `h₂=0, d=2, ℓ=5` → byte `0x2A` (42)
   - Output: `bytes=[0x2A]`
2. **Three ops (seq+par)** — `evaluate@c21 . copy@c05 || swap@c72`
   - Sigils: `c21→0x2A`, `c05→0x0A`, `c72→0xC0`
   - Output bytes (leaf order left→right inside branches): `[0x2A, 0x0A, 0xC0]`
3. **Prefixed transform** — `R+1@ (copy@c05 . evaluate@c21)`
   - `c05 (h₂,d,ℓ)=(0,0,5) → R+1 ⇒ (1,0,5) ⇒ ci'= 24*1 + 0 + 5 = 29 → byte 0x1A`
   - `c21 (0,2,5) → R+1 ⇒ (1,2,5) ⇒ ci'= 24*1 + 16 + 5 = 45 → byte 0x2E`
   - Output: `[0x1A, 0x2E]`
4. **Postfix transforms** — `c42^+3~@17`
   - `c42: (1,1,2)`; `T+3 ⇒ (1,1,5)`; `~ ⇒ (1,2,5)`; page `λ=17`
   - `ci' = 24*1 + 16 + 5 = 45 → byte 0x2E`; `addr = 256*17 + 0x2E = 4398`
5. **Context marching** — `T+4@ c00`
   - `c00: (0,0,0) → (0,0,4) = ci'=4 → byte 0x10`
6. **Mirror modality** — `M@ c13`
   - `c13: (0,1,5) → (0,2,5) = ci'=21 → byte 0x2A`
7. **Rotate+twist** — `R+2 T+3 @ c07`
   - `c07: (0,0,7) → (2,0,2) = ci'=50 → byte 0x84`
8. **Error: out of range** — `c96` → **parse error** (class index must be 0..95)

### 7.2 Operational (word) mode (schematic words)

9. `evaluate@c21 . copy@c05 || swap@c72`
   - Lowered (one possible): `[phase(0),evaluate, copy,mode(0),ctx(5)] ⊗ [swap]`
10. `scope(2, split@c13)` ≡ `R+2@ (split@c13)`
    - Lowers to `ρ² · [split,ctx(5)] · ρ^{-2}` then normalizes to a leaf with `h₂=2`.

---

## 8) Error Handling

- **Syntax:** unexpected token, missing `)` etc.
- **Range:** `cN` not in 0..95; `λ` not in 0..47; twist/rotate not integer.
- **Typing:** invalid composition under the 7‑generator typing rules (flag at lowering time).

---

## 9) Reference Algorithms (precise)

```ts
function decode(ci: number) {
  const h2 = Math.floor(ci / 24);
  const di = Math.floor((ci % 24) / 8);
  const l = ci % 8;
  return { h2: ((h2 % 4) + 4) % 4, d: di, l: ((l % 8) + 8) % 8 };
}
function applyXform(
  sig: { h2: number; d: number; l: number },
  X: { R?: number; T?: number; M?: boolean },
) {
  const h2 = (sig.h2 + (X.R || 0)) & 3; // mod 4
  const l = (sig.l + (X.T || 0)) & 7; // mod 8
  const d = X.M ? (sig.d === 1 ? 2 : sig.d === 2 ? 1 : 0) : sig.d;
  return { h2, d, l };
}
function encodeByte(sig: { h2: number; d: number; l: number }) {
  const h2 = sig.h2,
    d = sig.d,
    l = sig.l;
  const b1 = l & 1,
    b2 = (l >> 1) & 1,
    b3 = (l >> 2) & 1;
  const b4 = d == 1 ? 1 : 0,
    b5 = d == 2 ? 1 : 0; // (00,10,01) for d=0,1,2
  const b6 = h2 & 1,
    b7 = (h2 >> 1) & 1,
    b0 = 0;
  return (b7 << 7) | (b6 << 6) | (b5 << 5) | (b4 << 4) | (b3 << 3) | (b2 << 2) | (b1 << 1) | b0;
}
```

---

## 10) Two‑Page Reference (print)

### Page 1 — Symbols & Semantics

- **Triple:** `(h₂,d,ℓ)` = **scope**, **modality**, **context**.
- **Visual:** cardinal notch; center (•/▲cw/▲ccw); 8‑dot inner ring.
- **Mapping:** `ci = 24*h₂ + 8*d + ℓ` → **canonical byte** (with `b0=0`).
- **Transform group:** `R` (mod‑4), `T` (mod‑8), `M` (flip modality).
- **Sigil→Op:** `g@cℓ` lowers to 7‑generator words parameterized by `(h₂,d,ℓ)`.
- **Belt:** `addr = 256*λ + byte`.

### Page 2 — Grammar & Laws

- **EBNF** (see §1)
- **Composition laws:** assoc/comm/unit for `∘`/`⊗`.
- **Distribution:** `R/T/M` distribute over `∘,⊗` and commute to leaves.
- **Macros:** `NOT = M∘T₄`; `AND = merge(consume) after ⊗`; `OR = merge(produce) after ⊗`.
- **Errors:** syntax, range, typing.

To print: set margins narrow; scale 90–95%; this doc is designed to split at the page break above.

---

## 11) Next Steps (optional)

- Emit a **JSON test pack** (inputs, AST, bytes, addrs, lowered words).
- Provide a tiny **web demo** (textarea → parse → show bytes/addresses and words).
- Extend `M` with axis‑selective reflections for `h₂,ℓ` if desired.
