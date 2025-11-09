# Hologram IR (HGIR) Specification

**Version:** v1.0‑draft  
**Date:** 2025‑10‑18  
**Status:** Draft for implementation  
**Authority:** UOR Foundation — Atlas / Hologram Program

> HGIR is the single, canonical intermediate representation for authoring Atlas kernels. It is Atlas‑only: every operation corresponds to Atlas semantics and lowers to the Atlas ISA and runtime without host‑side computation modes.

---

## 1. Scope and Goals

HGIR provides a portable, SSA‑based kernel IR used by hologram‑stdlib and other frontends. It specifies:

- Program structure (module → kernels → blocks → ops),
- Types, constants, and attributes,
- Builtins (thread/grid indices),
- Scalar and memory operations,
- Atlas structural operations (Φ boundary mapping, mirror, neighbors, unity),
- Resonance operations with exact rational semantics,
- Validation and determinism rules,
- A textual syntax and a compact binary format.

This document is **normative** for producer/consumer conformance.

---

## 2. Execution Model

- **SPMD kernels.** A kernel runs across an implementation‑defined grid; builtins expose `global_id`, `local_id`, `block_id`, and `grid_dim` where applicable.
- **Atlas space.** All memory is a flat 64‑bit global address space governed by Atlas structures. Kernels may opt into the **boundary lens (Φ)** via `uses_boundary=true` and `BOUND.MAP` ops.
- **Phases.** Host controls phases. Kernels are executed within a phase epoch; kernels **MUST NOT** advance phase.
- **Determinism.** Given the same inputs and Atlas structures, a kernel’s observable effects are deterministic. Resonance reductions are exact (see §7).

---

## 3. Program Structure

```
Module
  ├─ Kernel* (functions with Kernel ABI)
  │    ├─ Attributes (metadata)
  │    ├─ Parameters (typed)
  │    └─ Blocks (CFG)
  ├─ Constants (pool)
  └─ Tables (optional per‑module metadata)
```

- **SSA.** All non‑memory values are in Static Single Assignment form. Dominance rules apply.
- **Side effects.** Memory and Atlas state changes (e.g., `STG`, `RES.ACCUM`) are effectful and ordered by program order.

---

## 4. Types

Primitive scalar types:
- Integers: `i1, i8, i16, i32, i64, i128`, `u8, u16, u32, u64` (unsigned ops use `u*`).
- Floats: `f16, bf16, f32, f64`.
- Pointers: `ptr<T>`: pointer to global memory with element type `T` (opaque at ISA level; used for type checking and addressing).
- Ratio literal: `ratio` (compile‑time constant only). Runtime representation of resonance is handled by Atlas (see §7, §11.4).

Composite types (v1.0 minimal):
- Vectors: `<N x T>` for N∈{2,4,8,16}. (Optional for producers; consumers MUST accept.)
- Tuples/structs are **not** part of v1.0; producers lower aggregates into scalars/vectors.

---

## 5. Attributes

**Kernel attributes** (fixed semantics):
- `uses_boundary: bool` — kernel will use `BOUND.MAP` with Φ.
- `mirror_safe: bool` — kernel result invariant under `c ↔ mirror(c)`.
- `unity_neutral: bool` — operations are identity on the unity set.
- `phase_window: [u16,u16]` — legal phases.
- `neighbor_stride: u8` — max neighbor hops per step (0 if not used).

**Instruction attributes** (selected):
- `align: u32` on `LDG/STG` (power‑of‑two in bytes; default natural alignment of `T`).
- `volatile: bool` on `LDG/STG` (defaults to false).

---

## 6. Builtins

- `global_id : u32` — linear thread id in [0, N).
- `local_id  : u32` — thread id within a block/workgroup.
- `block_id  : u32`, `grid_dim : u32`, `block_dim : u32` — optional, backend‑dependent and stable per invocation.
- `class_id  : u8` — current resonance class (when provided by launch context or loops using neighbors).
- `phase     : u16` — current phase (read‑only; no write op exists in HGIR).

Builtins are obtained via ops in §8.1.

---

## 7. Resonance (Exact Rational Semantics)

Resonance accumulators `R[c]` are exact rationals in canonical form. HGIR exposes a single operation:

```
RES.ACCUM  (class: u8, numer: iN, denom: uN)   // N ∈ {32,64,128}
```

Semantics (single rule):
1. Let `R[c] = n/d`, input is `a/b` with `b≠0`.
2. Compute `n' = n·b + a·d`, `d' = d·b`.
3. Reduce by `g=gcd(|n'|, d')`, set `n''=n'/g`, `d''=d'/g`.
4. Ensure `d''>0` (move sign to `n''`), and if `n''==0` set `d''=1`.
5. Write back `R[c]=n''/d''`.

Observability: any readback via host uses canonical binary encoding defined by the runtime. HGIR does not define a read op; kernels cannot read `R[c]` in v1.0.

---

## 8. Operations

### 8.1 Builtin & Control Flow
- `BUILTIN.GLOBAL_ID() -> u32`
- `BUILTIN.LOCAL_ID() -> u32`
- `BUILTIN.BLOCK_ID() -> u32`
- `BUILTIN.GRID_DIM() -> u32`
- `BUILTIN.BLOCK_DIM() -> u32`
- `PHASE.READ() -> u16` (read‑only)
- `RET()`
- `BR(label)`
- `BR.IF(pred: i1, then: label, else: label)`
- `SWITCH(idx: u32, default: label, [case→label]...)`

### 8.2 Integer & Floating Arithmetic
`ADD, SUB, MUL, DIV, REM` (typed variants: `.iN`, `.uN`, `.f32`, `.f64`, etc.)
`MIN, MAX` (numeric types)
`NEG` (signed/float), `ABS` (signed/float)

### 8.3 Logic & Bit Operations
`AND, OR, XOR` (integers), `NOT`
`SHL, LSHR (logical), ASHR (arithmetic)`
`CLZ, CTZ, POPCNT` (u32/u64)

### 8.4 Comparisons & Select
`CMP.EQ, CMP.NE, CMP.LT, CMP.LE, CMP.GT, CMP.GE` (signed/unsigned/float variants) → `i1`
`SELECT(pred: i1, t: T, f: T) -> T`

### 8.5 Memory Operations (Global)
- `LDG.T(ptr<T>, idx: u32 [, align]) -> T`  // Loads `*(ptr + idx)`
- `STG.T(ptr<T>, idx: u32, value: T [, align])`
- `MEMCPY(ptr<u8> dst, ptr<u8> src, bytes: u32 [, align])` (lowered to loop of LDG/STG)  
- `MEMSET(ptr<u8> dst, byte: u8, bytes: u32 [, align])` (lowered to loop)

### 8.6 Boundary Lens (Φ) & Atlas Structure
- `BOUND.MAP(phi: Φ, class: u8, x: u8, y: u16) -> ptr<u8>`  
  Returns a byte pointer into global memory. Producers typically cast to `ptr<T>` via `PTR.CAST` with alignment guarantees.
- `PTR.CAST(ptr<u8> p) -> ptr<T>`  // type‑checked cast with alignment assertion
- `NBR.GET(class: u8, idx: u8) -> u8`  // neighbor of class
- `MIRROR(class: u8) -> u8`
- `UNITY.TEST(class: u8, coord: …) -> i1` (v1.0: the `coord` form is reserved; test is class‑local for now)

### 8.7 Conversions
`TRUNC, ZEXT, SEXT, FPTOI, ITOFP, BITCAST`

### 8.8 Vector Ops (if available)
`VLDG, VSTG, VADD, VSUB, VMUL, VREDUCE.ADD` etc., for `<N x T>`; must be semantically equivalent to scalar expansion.

---

## 9. Kernel ABI

- **Parameters:** passed as SSA values: pointers, scalars, Φ descriptors, and small POD structs if needed.
- **Return:** kernels return `void` (effects through memory and resonance).
- **Attributes:** must be attached at kernel definition; consumers validate before launch.

---

## 10. Textual Syntax

### 10.1 Lexical
- Identifiers: `%v0`, `%sum`, `@kernel`, `^bb0`.
- Types: `i32`, `f32`, `ptr<f32>`, `<4 x f32>`.
- Literals: `i32 42`, `f32 1.0`, `u8 7`.

### 10.2 Grammar (abridged)
```
module ::= 'module' string '{' kernel* const* '}'
kernel ::= 'kernel' '@'ident '(' params? ')' attrs? '{' block+ '}'
params ::= param (',' param)*
param  ::= '%'ident ':' type
attrs  ::= 'attributes' '{' attr (',' attr)* '}'
block  ::= '^'ident ':' inst+
inst   ::= result? '=' op | op
result ::= '%'ident
op     ::= mnemonic (operands?) (attrlist?)
```

### 10.3 Example — Vector Add
```
module "hologram.stdlib" {
  kernel @vec_add(%A: ptr<f32>, %B: ptr<f32>, %C: ptr<f32>, %N: u32)
    attributes { uses_boundary=false, mirror_safe=true, unity_neutral=true, phase_window=[0,767] } {
    ^entry:
      %gid = builtin.global_id()
      %p   = cmp.lt.u32 %gid, %N
      br_if %p, ^do, ^end
    ^do:
      %a = ldg.f32 %A, %gid
      %b = ldg.f32 %B, %gid
      %s = add.f32 %a, %b
      stg.f32 %C, %gid, %s
      br ^end
    ^end:
      ret
  }
}
```

### 10.4 Example — Boundary Transpose (Φ)
```
module "hologram.stdlib" {
  kernel @transpose_boundary(%phi: Phi, %cls: u8, %w: u8, %h: u16)
    attributes { uses_boundary=true, mirror_safe=false, unity_neutral=true, phase_window=[0,767] } {
    ^entry:
      %x  = builtin.local_id()
      %y  = builtin.block_id()  // simple tiling example
      %p0 = bound.map %phi, %cls, %x, %y
      %p1 = bound.map %phi, %cls, %y, %x
      %v  = ldg.u8 %p0, 0
      stg.u8 %p1, 0, %v
      ret
  }
}
```

---

## 11. Binary Format (v1.0)

### 11.1 File Layout
```
+------------------+---------------------------------------------+
| Magic "HGIR"     | 4 bytes                                     |
| Version          | u16 (0x0100 for v1.0)                        |
| Reserved         | u16 (0)                                      |
| Section Count    | u16                                          |
| Section Table    | section_count × SectionHeader                |
+------------------+---------------------------------------------+
```
`SectionHeader { kind: u16, flags: u16, offset: u32, size: u32 }`

Section kinds (in required order):
1. **STR**  (kind=1) — UTF‑8 string table.
2. **TYP**  (2) — type table.
3. **KMD**  (3) — kernel metadata (attributes, params).
4. **CFG**  (4) — blocks and control‑flow graph.
5. **INS**  (5) — instructions stream (RLE‑encoded opcodes + operand indices).
6. **CST**  (6) — constants pool (scalars, vector splats, ratio literals → runtime canonical encoding).
7. **TAB**  (7) — optional module tables (e.g., Φ descriptor templates).

Consumers **MUST** ignore unknown sections with the high bit set in `kind`.

### 11.2 Instruction Encoding

```
Instr {
  opcode: u16,
  n_operands: u8,
  n_attrs: u8,
  results: u8,      // 0 or 1 in v1.0
  operand_idx[n],   // indices into value table or immediates pool
  attr_idx[m],
}
```
- Values are identified by a compact index; defining instructions allocate a new value id sequentially.
- Immediates (small integers) may be inlined via a 1‑byte tag + LEB128 payload.

### 11.3 Opcodes (subset)
```
0x0001 RET
0x0002 BR
0x0003 BR_IF
0x0010 BUILTIN_GLOBAL_ID
0x0011 BUILTIN_LOCAL_ID
0x0012 BUILTIN_BLOCK_ID
0x0013 BUILTIN_GRID_DIM
0x0014 BUILTIN_BLOCK_DIM
0x0020 ADD
0x0021 SUB
0x0022 MUL
0x0023 DIV
0x0024 REM
0x0030 AND
0x0031 OR
0x0032 XOR
0x0033 NOT
0x0034 SHL
0x0035 LSHR
0x0036 ASHR
0x0040 CMP
0x0041 SELECT
0x0050 LDG
0x0051 STG
0x0060 MEMCPY
0x0061 MEMSET
0x0070 BOUND_MAP
0x0071 PTR_CAST
0x0072 NBR_GET
0x0073 MIRROR
0x0074 UNITY_TEST
0x0080 CONVERT   // TRUNC/EXT/FPTOI/ITOF/BITCAST via subkind
0x0090 RES_ACCUM
```
Typed variants are specified by per‑instruction type operands or subkinds.

### 11.4 Constants Encoding
- Scalars encoded little‑endian (IEEE‑754 for floats).
- Ratio literals use the runtime’s canonical rational container (see Atlas Runtime ABI). HGIR stores an index to this blob; consumers pass it through to `RES.ACCUM` immediates where applicable.

---

## 12. Validation Rules

- **SSA dominance:** uses must be dominated by their defs.
- **Type safety:** operands/results must match instruction typing rules.
- **Memory:** `LDG/STG` pointers must be of `ptr<T>`; `align` must be ≥ natural alignment.
- **Boundary:** if `uses_boundary=true`, any pointer derived from boundary coordinates **MUST** originate from `BOUND.MAP` within the kernel or from a validated Φ pointer parameter.
- **Neighbors:** traversals between classes used by the kernel **MUST** be produced by `NBR.GET`; consumers may instrument runtime validation.
- **Resonance:** `RES.ACCUM` denominators must be non‑zero at IR level; producers MUST provide literals or values guaranteed non‑zero (enforced by runtime as well).

Failures are producer errors (reject load) or runtime validation errors (reject launch) depending on when they can be detected.

---

## 13. Determinism & Optimization

- Reordering of pure ops is allowed if it preserves program order w.r.t. memory and Atlas effects.
- Common subexpression elimination is permitted for pure ops.
- Vectorization is permitted if it preserves per‑element semantics.
- Reductions inside a kernel may use tree associations **only** if the exact rational result matches sequential accumulation.

---

## 14. Mapping to Atlas ISA

- **Arithmetic/Logic/Memory** map 1:1 to ISA arithmetic and global memory ops.
- **BOUND.MAP** lowers to the runtime’s Φ address calculation; emitted address is used by `LDG/STG`.
- **NBR.GET/MIRROR/UNITY.TEST** lower to table lookups provided by the runtime.
- **RES.ACCUM** lowers to the canonical rational accumulation opcode; no alternative paths exist.
- **BUILTIN** ops map to launch‑time constants or device intrinsics.

---

## 15. Producer & Consumer Requirements

**Producers (e.g., hologram‑stdlib):**
- MUST emit well‑formed SSA with validated types and attributes.
- SHOULD minimize `BOUND.MAP` calls by hoisting loop‑invariant coordinates.
- MUST avoid host‑side computation for any `ops::*` emission.

**Consumers (atlas‑runtime and backends):**
- MUST validate attributes vs. kernel body (e.g., `uses_boundary` flag matches usage).
- MUST enforce boundary windows, neighbor legality, mirror/unity contracts.
- MUST implement exact rational resonance semantics.

---

## 16. Examples (Informative)

### 16.1 Sum Reduction (linear buffer)
```
kernel @sum(%A: ptr<f32>, %N: u32, %Out: ptr<f32>) attributes { uses_boundary=false, mirror_safe=true, unity_neutral=true, phase_window=[0,767] } {
  ^entry:
    %gid = builtin.global_id()
    %pred = cmp.lt.u32 %gid, %N
    br_if %pred, ^body, ^end
  ^body:
    %v = ldg.f32 %A, %gid
    // ... tree reduction pattern elided ...
    // final write by lane 0 of each group
    stg.f32 %Out, 0, %v_reduced
    br ^end
  ^end:
    ret
}
```

### 16.2 Resonance Update (literal ratio)
```
kernel @tick(%cls: u8) attributes { uses_boundary=false, mirror_safe=false, unity_neutral=true, phase_window=[0,767] } {
  ^entry:
    // Accumulate +1/3 into class %cls resonance
    res.accum %cls, i32 1, u32 3
    ret
}
```

---

## 17. Change Log
- **v1.0‑draft (2025‑10‑18):** Initial public draft.

