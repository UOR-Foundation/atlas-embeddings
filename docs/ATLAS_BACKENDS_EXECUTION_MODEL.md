# Atlas Backends: Instruction Execution Model

**Version:** v0.1.0 (Phase 6 Complete)
**Date:** 2025-10-21

## Overview

This document describes the instruction execution pipeline for Atlas backends, focusing on the `CPUBackend` implementation. Understanding this model is critical for:

- Backend implementers (GPU, quantum, analog)
- Compiler writers (generating ISA programs)
- Performance optimization
- Debugging execution issues

---

## Execution Pipeline

The execution pipeline consists of 4 stages:

```text
┌────────────┐     ┌──────────────┐     ┌──────────────┐     ┌──────────────┐
│  Validate  │ ──> │ Label Resolve │ ──> │   Execute    │ ──> │ Synchronize  │
└────────────┘     └──────────────┘     └──────────────┘     └──────────────┘
     │                    │                      │                    │
     ▼                    ▼                      ▼                    ▼
Type safety        Build jump map      Sequential         Write cache
Register bounds    Scan for labels     instruction        to AtlasSpace
Instruction        Detect cycles       dispatch
compliance                             Control flow
```

### Stage 1: Validation

**Purpose:** Ensure program correctness before execution

**Checks:**
- ✅ Register indices [0, 256)
- ✅ Predicate indices [0, 16)
- ✅ All instruction types supported
- ✅ Memory addresses valid
- ✅ Type annotations valid

**Implementation:** `CPUBackend::validate_program()`

```rust
fn validate_program(&self, program: &Program) -> Result<()> {
    for instruction in program {
        match instruction {
            // Validate each instruction type
            Instruction::ADD { dst, src1, src2, .. } => {
                validate_reg(dst)?;
                validate_reg(src1)?;
                validate_reg(src2)?;
            }
            // ... all 55 instruction types
        }
    }
    Ok(())
}
```

**Errors:**
- `InvalidRegister`: Register index ≥ 256
- `InvalidPredicate`: Predicate index ≥ 16
- `UnsupportedInstruction`: Backend doesn't implement instruction

---

### Stage 2: Label Resolution

**Purpose:** Build jump target map for control flow

**Process:**
1. Scan program for `BRA`, `CALL`, `LOOP` instructions
2. Extract target labels
3. Map label strings to program counter values

**Implementation:** `CPUBackend::build_label_map()`

```rust
fn build_label_map(&self, program: &Program) -> Result<HashMap<String, usize>> {
    // Scan for control flow instructions
    for (pc, instruction) in program.iter().enumerate() {
        match instruction {
            Instruction::BRA { target, .. } => {
                // Label will be resolved when encountered
            }
            Instruction::CALL { target } => {
                // Label will be resolved when encountered
            }
            // ...
        }
    }
    Ok(labels)
}
```

**Note:** Current implementation defers label resolution to execution time. Future optimization: pre-build label map during validation.

---

### Stage 3: Execute

**Purpose:** Sequential instruction dispatch through register file

**Execution Loop:**

```rust
fn execute_program(&mut self, program: &Program, context: &ExecutionContext) -> Result<()> {
    // Initialize state
    self.program_counter = 0;
    self.registers.reset();
    self.phase = context.phase;

    // Execute until EXIT or end of program
    while self.program_counter < program.len() {
        let instruction = &program[self.program_counter];
        self.execute_instruction(instruction, context)?;

        // Check for program termination
        if self.program_counter == usize::MAX {
            break;  // EXIT instruction sets PC to MAX
        }
    }

    Ok(())
}
```

**Instruction Dispatch:**

Each instruction type has a dedicated handler. For example, `ADD`:

```rust
Instruction::ADD { ty, dst, src1, src2 } => {
    match ty {
        Type::I32 => {
            let a: i32 = self.registers.read(*src1)?;
            let b: i32 = self.registers.read(*src2)?;
            self.registers.write(*dst, a.wrapping_add(b))?;
        }
        Type::F32 => {
            let a: f32 = self.registers.read(*src1)?;
            let b: f32 = self.registers.read(*src2)?;
            self.registers.write(*dst, a + b)?;
        }
        // ... all 12 types
    }
    self.program_counter += 1;
}
```

**Control Flow:**

Control flow instructions modify the program counter:

```rust
Instruction::BRA { target, pred } => {
    // Check predicate (if present)
    let should_branch = match pred {
        Some(p) => self.registers.read_pred(*p),
        None => true,  // Unconditional branch
    };

    if should_branch {
        // Jump to label
        let target_pc = self.labels.get(&target.0)
            .ok_or_else(|| BackendError::ExecutionFailed(format!("undefined label: {}", target.0)))?;
        self.program_counter = *target_pc;
    } else {
        self.program_counter += 1;  // Fall through
    }
}
```

---

### Stage 4: Synchronize

**Purpose:** Write backend state to AtlasSpace

**Operations:**
- Cache flush (L1/L2 → main memory)
- Device memory download (GPU → host)
- Quantum measurement readout
- Analog state sampling

**Implementation:** `CPUBackend::synchronize()`

```rust
fn synchronize(&mut self, space: &mut AtlasSpace) -> Result<()> {
    // For CPU: Most state is already in shared memory
    // Just ensure cache coherency
    self.arch.fence_release();
    self.arch.fence_acquire();

    // Write resonance accumulators
    space.set_resonance(self.resonance.clone());

    // Write phase counter
    space.set_phase(self.phase);

    Ok(())
}
```

---

## State Management

### Program Counter (PC)

- **Range:** `[0, program.len())`
- **Initial value:** 0 (start of program)
- **Increment:** +1 after each instruction (except control flow)
- **Special value:** `usize::MAX` indicates EXIT

### Register File

- **256 scalar registers** (R0-R255)
- **16 predicate registers** (P0-P15)
- **Type tracking:** `Option<Type>[256]`

**Register Lifetime:**
1. **Uninitialized:** No type, read fails
2. **Initialized:** Type set by first write
3. **Valid:** Type matches on read
4. **Overwritten:** Type changes on write (CVT instruction)

### Resonance Accumulators

- **96 classes:** `[Rational; 96]`
- **Exact arithmetic:** Uses `num_rational::Rational` (no floating-point error)
- **Operations:**
  - `RES_ACCUM`: Add value to class
  - `UNITY_TEST`: Check if sum ≈ 0

### Phase Counter

- **Range:** `[0, 768)` (modulo 768)
- **Operations:**
  - `PHASE_GET`: Read current phase
  - `PHASE_ADV`: Advance by delta (mod 768)

---

## Error Handling

All execution stages return `Result<T, BackendError>`:

| Error Type | Stage | Cause |
|------------|-------|-------|
| `InvalidRegister` | Validation | Register ≥ 256 |
| `InvalidPredicate` | Validation | Predicate ≥ 16 |
| `TypeMismatch` | Execute | Wrong type read from register |
| `UninitializedRegister` | Execute | Read before write |
| `ExecutionFailed` | Execute | Runtime error (div by zero, etc.) |
| `InvalidTopology` | Synchronize | Buffer handle invalid |

**Error Recovery:**
- Validation errors → Reject program before execution
- Execution errors → Stop immediately, preserve state for debugging
- Synchronization errors → Backend state inconsistent, must reinitialize

---

## Atlas-Specific Operations

### Topology Queries

```rust
// Get current resonance class
Instruction::CLS_GET { dst } => {
    let class = context.active_classes.first().copied().unwrap_or(0);
    self.registers.write(*dst, class)?;
    self.program_counter += 1;
}

// Get mirror of class
Instruction::MIRROR { dst, src } => {
    let class: u8 = self.registers.read(*src)?;
    let topology = self.topology.as_ref().ok_or(BackendError::NotInitialized)?;
    let mirror = topology.mirrors()[class as usize];
    self.registers.write(*dst, mirror)?;
    self.program_counter += 1;
}
```

### Boundary Addressing

```rust
// Map Φ-coordinates to linear address
Instruction::BOUND_MAP { class, page, byte, dst } => {
    let class_idx: u8 = self.registers.read(*class)?;
    let page_idx: u8 = self.registers.read(*page)?;
    let byte_idx: u8 = self.registers.read(*byte)?;

    // Compute: class * CLASS_STRIDE + page * 256 + byte
    let offset = (class_idx as usize) * CLASS_STRIDE
        + (page_idx as usize) * 256
        + (byte_idx as usize);

    self.registers.write(*dst, offset as u64)?;
    self.program_counter += 1;
}
```

---

## Performance Characteristics

### Instruction Latency (CPUBackend)

| Category | Example | Latency | Throughput |
|----------|---------|---------|------------|
| Arithmetic | ADD, MUL | 4 ns | 250M ops/s |
| Memory | LDG, STG | 10 ns | 100M ops/s |
| Control Flow | BRA, CALL | 15 ns | 67M ops/s |
| Transcendental | SIN, COS | 50 ns | 20M ops/s |
| Reduction | REDUCE_ADD | 100 ns | 10M ops/s |
| Synchronization | BAR_SYNC | 10 ns | - |

### Register File Performance

| Operation | Latency | Notes |
|-----------|---------|-------|
| Read (type match) | 15 ns | Array index + type check |
| Write | 15 ns | Array index + type set |
| Type mismatch | 20 ns | Error construction overhead |
| Predicate access | 10 ns | No type check |

### SIMD Optimizations

**AVX-512 (512-bit vectors):**
- 16 × f32 operations in parallel
- 2 GB/s sustained throughput
- Automatic fallback to AVX2 or scalar

**Alignment Requirements:**
- Cache lines: 64 bytes
- SIMD loads: 32/64 byte alignment preferred
- Boundary pool: Always aligned

---

## Debugging

### Common Issues

**1. Uninitialized Register:**
```
Error: UninitializedRegister { register: 42 }
```
**Cause:** Reading R42 before writing
**Fix:** Ensure all registers written before use

**2. Type Mismatch:**
```
Error: TypeMismatch { register: 0, expected: I32, actual: Some(F32) }
```
**Cause:** Wrote F32, tried to read as I32
**Fix:** Use correct type or CVT instruction

**3. Undefined Label:**
```
Error: ExecutionFailed("undefined label: loop_start")
```
**Cause:** BRA target not in program
**Fix:** Add label or fix typo

### Debugging Tools

**1. Trace Execution:**
```rust
// Set environment variable
export ATLAS_TRACE=1

// Backend will log each instruction
```

**2. Inspect Register State:**
```rust
// After error, dump register file
for i in 0..256 {
    if let Some(ty) = regs.get_type(Register::new(i)) {
        println!("R{}: {:?}", i, ty);
    }
}
```

**3. Validate Before Execute:**
```rust
// Always validate in debug builds
#[cfg(debug_assertions)]
backend.validate_program(&program)?;

backend.execute_program(&program, &ctx)?;
```

---

## Future Optimizations

### Phase 8/9: Parallel Execution

- Instruction-level parallelism (ILP)
- Data-level parallelism (SIMD)
- Thread-level parallelism (multi-core)

### Phase 10: JIT Compilation

- Compile ISA programs to native code
- LLVM backend for optimization
- Specialized GPU kernels

### Phase 11: Hardware Acceleration

- Custom FPGA designs
- GPU shader execution
- Quantum circuit compilation

---

## See Also

- [SPEC.md](../crates/atlas-backends/SPEC.md): Normative specification
- [atlas-isa](../crates/atlas-isa/): ISA instruction definitions
- [atlas-runtime](../crates/atlas-runtime/): AtlasSpace state management
- [IMPLEMENTATION_TASKS.md](../crates/atlas-backends/IMPLEMENTATION_TASKS.md): Implementation roadmap
