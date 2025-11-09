# Migration Guide: Vec<Instruction> to Program Struct

**Version**: 1.0
**Date**: 2025-10-22
**Applies to**: atlas-isa v0.2.0+

## Overview

Atlas ISA v0.2.0 introduces a breaking change to the `Program` type to support control flow instructions with label metadata. This guide helps you migrate from the old type alias to the new struct.

## What Changed

### Before (v0.1.x)
```rust
pub type Program = Vec<Instruction>;
```

### After (v0.2.0+)
```rust
#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub instructions: Vec<Instruction>,
    pub labels: HashMap<String, usize>,
}
```

## Migration Strategies

### Strategy 1: Use Compatibility Helpers (Recommended)

The `Program` struct implements `From<Vec<Instruction>>` and `From<Program> for Vec<Instruction>` for easy conversion.

**Pattern A: Inline conversion with `.into()`**
```rust
// Before
let program: Program = vec![
    Instruction::ADD { ... },
    Instruction::MUL { ... },
];

// After
let program: Program = vec![
    Instruction::ADD { ... },
    Instruction::MUL { ... },
].into();
```

**Pattern B: Explicit conversion with `Program::from_instructions()`**
```rust
// Before
let instructions = vec![Instruction::ADD { ... }];
let program: Program = instructions;

// After
let instructions = vec![Instruction::ADD { ... }];
let program = Program::from_instructions(instructions);
```

### Strategy 2: Update Field Access

If you previously indexed into the program or called methods on it, update to access the `.instructions` field.

**Iteration**
```rust
// Before
for instruction in program.iter() { ... }

// After
for instruction in program.instructions.iter() { ... }
```

**Length**
```rust
// Before
let len = program.len();

// After
let len = program.instructions.len();
```

**Indexing**
```rust
// Before
let inst = &program[0];

// After
let inst = &program.instructions[0];
```

**Push/extend**
```rust
// Before
program.push(Instruction::EXIT);

// After
program.instructions.push(Instruction::EXIT);
```

### Strategy 3: Add Label Support (For Control Flow)

If your program uses control flow instructions (BRA, CALL, LOOP), you must add labels.

**Basic label usage**
```rust
let mut program = Program::new();

// Add label at current position
program.add_label("loop_start")?;
program.instructions.push(Instruction::LDG { ... });
program.instructions.push(Instruction::ADD { ... });

// Branch back to label
program.instructions.push(Instruction::BRA {
    target: Label("loop_start".to_string()),
    pred: None,
});
```

**Builder pattern**
```rust
use atlas_isa::{Program, Instruction, Label};

fn build_loop_program() -> Result<Program, ProgramError> {
    let mut prog = Program::new();

    prog.add_label("start")?;
    prog.instructions.extend(vec![
        Instruction::MOV { ... },
        Instruction::ADD { ... },
    ]);

    prog.add_label("loop")?;
    prog.instructions.push(Instruction::LOOP {
        counter: Register(0),
        target: Label("loop".to_string()),
    });

    prog.instructions.push(Instruction::EXIT);
    Ok(prog)
}
```

## Common Migration Scenarios

### Scenario 1: Test Code

**Before**
```rust
#[test]
fn test_execution() {
    let program: Program = vec![
        Instruction::MOV { ty: Type::F32, dst: Register(0), src: Register(1) },
        Instruction::EXIT,
    ];
    backend.execute_program(&program, &ctx).unwrap();
}
```

**After**
```rust
#[test]
fn test_execution() {
    let program: Program = vec![
        Instruction::MOV { ty: Type::F32, dst: Register(0), src: Register(1) },
        Instruction::EXIT,
    ].into();
    backend.execute_program(&program, &ctx).unwrap();
}
```

### Scenario 2: Program Construction

**Before**
```rust
let mut program: Program = Vec::new();
program.push(Instruction::LDG { ... });
program.push(Instruction::EXIT);
```

**After (Option A: Convert at end)**
```rust
let mut instructions = Vec::new();
instructions.push(Instruction::LDG { ... });
instructions.push(Instruction::EXIT);
let program = Program::from_instructions(instructions);
```

**After (Option B: Use Program directly)**
```rust
let mut program = Program::new();
program.instructions.push(Instruction::LDG { ... });
program.instructions.push(Instruction::EXIT);
```

### Scenario 3: Backend Implementation

**Before**
```rust
fn validate_program(&self, program: &Program) -> Result<()> {
    for (pc, instruction) in program.iter().enumerate() {
        self.validate_instruction(instruction, pc)?;
    }
    Ok(())
}
```

**After**
```rust
fn validate_program(&self, program: &Program) -> Result<()> {
    for (pc, instruction) in program.instructions.iter().enumerate() {
        self.validate_instruction(instruction, pc)?;
    }
    Ok(())
}
```

### Scenario 4: Control Flow Programs

**Before (Not possible - no label support)**
```rust
// Could not create labeled programs
```

**After**
```rust
fn factorial_program() -> Result<Program, ProgramError> {
    let mut prog = Program::new();

    // Initialize: r0 = n, r1 = 1 (result), r2 = 1 (counter)
    prog.add_label("start")?;
    prog.instructions.push(Instruction::MOV {
        ty: Type::U32,
        dst: Register(1),
        src: Register(10),  // Load 1 from r10
    });

    prog.add_label("loop")?;
    prog.instructions.push(Instruction::MUL {
        ty: Type::U32,
        dst: Register(1),
        src1: Register(1),
        src2: Register(2),
    });
    prog.instructions.push(Instruction::ADD {
        ty: Type::U32,
        dst: Register(2),
        src1: Register(2),
        src2: Register(10),  // Add 1
    });
    prog.instructions.push(Instruction::SETcc {
        ty: Type::U32,
        cond: Condition::LE,
        dst: Predicate(0),
        src1: Register(2),
        src2: Register(0),
    });
    prog.instructions.push(Instruction::BRA {
        target: Label("loop".to_string()),
        pred: Some(Predicate(0)),
    });

    prog.instructions.push(Instruction::EXIT);
    Ok(prog)
}
```

## Error Handling

The new `Program` type introduces error handling for label operations:

```rust
use atlas_isa::{Program, ProgramError};

let mut prog = Program::new();

// Duplicate label error
prog.add_label("start")?;
prog.add_label("start")?;  // Error: DuplicateLabel("start", 0)

// Undefined label - detected by backend during validation
prog.instructions.push(Instruction::BRA {
    target: Label("undefined".to_string()),
    pred: None,
});
// Backend.validate_program() will return UndefinedLabel error
```

## Checklist

- [ ] Replace `vec![...]` with `vec![...].into()` for Program construction
- [ ] Update `program.iter()` to `program.instructions.iter()`
- [ ] Update `program.len()` to `program.instructions.len()`
- [ ] Update `program[i]` to `program.instructions[i]`
- [ ] Update `program.push()` to `program.instructions.push()`
- [ ] Add labels for control flow instructions (BRA, CALL, LOOP)
- [ ] Handle `ProgramError` from label operations
- [ ] Run tests to verify migration

## Verification

After migration, verify your code compiles and all tests pass:

```bash
# Compile check
cargo build --workspace

# Run all tests
cargo test --workspace

# Check for warnings
cargo clippy --workspace -- -D warnings
```

## Support

For questions or issues with migration:

1. Review the [Atlas ISA SPEC.md](../crates/atlas-isa/SPEC.md) §7.4
2. Check the [Program struct implementation](../crates/atlas-isa/src/instructions.rs)
3. See examples in [atlas-backends tests](../crates/atlas-backends/src/cpu.rs)

## Timeline

- **v0.1.x**: Old `Vec<Instruction>` type alias (deprecated)
- **v0.2.0**: New `Program` struct (current)
- **v0.3.0**: Compatibility helpers may be removed (future)

**Recommendation**: Migrate to the new `Program` struct immediately to prepare for control flow support.
