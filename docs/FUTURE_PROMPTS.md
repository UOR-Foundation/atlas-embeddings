Currently sigmatics generates a string that comprises actions as a AST and the SigmaticsCompiler compiles that string into a canonical generator sequence. This entire operation is performed at runtime. We need to move the compilation steps from the string into the build process at compile time.

Having the sigmatics compiler string generation will allow us to optimize the generator sequence for the specific hardware platforms, have known execution workflows, and remove overhead from the runtime.

This is a critical step in the development of the Hologram project. It will allow us to:

- Reduce the runtime overhead of the compiler
- Reduce the memory overhead of the compiler
- Reduce the time to compile the compiler
- Reduce the time to compile the compiler

I want you to propose a plan for how we can achieve this. The goal would be to take the hologram-codegen and hologram-kernel-runtime crates and use the generated kernels (inline and dylib) to generate the canonical generator sequence at compile time using the sigmatics structure.

The idea (perhaps naively) is to take the `schemas/*` which are functions written in python that represent a kernel. We'll take those and convert those functions into the sigmatics circuit string at compile time. From there, we'll take that string and compile it using the `hologram-codegen` to generate the canonical generator sequence to the instructions set forth by the `atlas-isa` so that backends can execute these "natively."

Effectively, we want these kernels written in python (and translated to JSON) that get compiled into sigmatics circuit string which then needs to be compiled into a `hologram-backends` `Program` struct which then is serialized into binary.

It's possible that the `hologram-codegen` and `hologram-kernel-runtime` crates become obsolete since we'll be using sigmatics to compile new functionality for `hologram-core` to utilize. Don't remove the crates until we're feature-complete with this set of features.

---

Based on my exploration of the codebase, I can see the architecture clearly. However, before proposing a comprehensive plan, I need to clarify some key architectural decisions that will significantly impact the implementation approach:
Clarifying Questions

1. Computational Model Mapping The Python schemas use a thread-based model (get_global_id(), parallel threads), while Sigmatics uses a class-based model (96 classes, each with 3,072 f32 elements). These are fundamentally different execution models. How should we bridge this gap?
   Option A: Map each thread operation to a class operation (thread idx → class idx)?
   Option B: Map entire vectors to class ranges (vector of N elements → classes 0..N/3072)?
   Option C: Define a new intermediate representation that can express both models?
2. Operation Coverage Not all Python kernel operations naturally map to Sigmatics generators:
   Simple element-wise ops (add, mul) → merge/mark generators ✅
   Reductions with atomics (sum, dot) → ReduceSum generator ✅
   Matrix multiply (gemm) with nested loops → ❓
   Quantum-inspired algorithms (amplitude amplification) → ❓
   Should we:
   Option A: Only convert operations that naturally fit Sigmatics (partial migration)?
   Option B: Extend Sigmatics with new generators to cover all operations?
   Option C: Use hybrid approach (Sigmatics for simple ops, direct ISA for complex ops)?
3. Source of Truth Currently Python schemas compile to Rust code. In the new architecture:
   Option A: Keep Python as source → generate Sigmatics strings → compile to ISA?
   Option B: Create new declarative format (JSON/TOML) that directly describes Sigmatics circuits?
   Option C: Write Sigmatics circuit strings directly as source (no Python)?
4. Binary Distribution For the compiled operations:
   Option A: One binary file per operation (vector_add.bin, vector_mul.bin)?
   Option B: Single bundled binary with all operations (stdlib.bin)?
   Option C: Inline as Rust code (const arrays of instructions)?
5. Backwards Compatibility hologram-core operations currently use direct GeneratorCall construction (zero-overhead, optimal). After this change:
   Option A: Keep existing direct construction for performance-critical paths?
   Option B: Replace all operations with new compiled binary format?
   Option C: Provide both interfaces (direct for internal, binary for user extensions)?
   Please clarify these architectural decisions so I can propose a detailed, concrete implementation plan.

We have some question for you first. I want you to answer these questions with a plan:

1. I think the `hologram-core` needs to be updated to map to the `hologram-backends` and the backend's isa. Before we can decide which computational model mapping makes sense, we need to figure out how the `hologram-core` wraps in. If the `hologram-core` maps to the backends, I think Option B make more sense
2. We don't want to extend sigmatics with new generators, what we really want are kernels that provide extra functionality to `hologram-core` which uses `altas` and the `hologram-backends` to provide complex functionality. Sigmatics is a way for us to generate these kernels in the most optimal way. Sigmatics has an auto-optimizer for a circuit builder so I **think** all the kernels should be able to be built using sigmatics. Does this make sense? If not, then I think we want to go with Option C, but please ask before assuming that's the answer.
3. Source of Truth: We want to go with Option B where the python code can be translated to JSON, YAML, or TOML that then sigmatics generates it's circuit from.
4. Option B: We want to ship a single binary with all stdlib operations, but we want to be able to load other binaries at runtime (dylib, for example).
5. Option C

I want you to update `hologram-core` so that it doesn't require any runtime code for sigmatics.

Also can we use rayon for the parallelization of the `execute()` function (the main execution loop) so that we can squeeze more performance in the nested loop? Additionally, I'd like to keep the zero-copy pattern so that we don't introduce more overhead with copying data around at runtime and instead use the reference to the memory and keep performance as the number 1 priority.

---

2. ⚠️ Sigmatics Auto-Optimizer: Can ALL Kernels Use It?
   Critical Question: Can complex operations (GEMM, convolution) be expressed as Sigmatics circuits? Analysis: ✅ Works Well for Sigmatics:
   Element-wise binary ops (add, mul, sub, div) → merge/split generators
   Element-wise unary ops (abs, sigmoid, tanh, relu) → merge with self-context
   Reductions (sum, min, max) → Dedicated ReduceSum/ReduceMin/ReduceMax
   Simple transformations → Pattern-based canonicalization applies
   ❓ Challenging for Sigmatics:
   GEMM (matrix multiply): Nested loops with accumulation
   for i in range(M):
   for j in range(N):
   for k in range(K):
   C[i,j] += A[i,k] _ B[k,j] # Accumulation across k
   Requires stateful accumulation across inner loop
   Not naturally expressible as single merge/split operation
   Would need sequence of operations per iteration
   Convolution: Sliding window with multiple accumulations
   for i in range(H_out):
   for j in range(W_out):
   for kh in range(kernel_h):
   for kw in range(kernel_w):
   out[i,j] += input[i+kh, j+kw] _ kernel[kh, kw]
   Similar accumulation challenge
   Complex indexing patterns
   My Recommendation: Option C (Hybrid Approach) Reason: While Sigmatics' auto-optimizer is excellent for simple operations, complex multi-loop operations with accumulation don't naturally map to the 7 generators. A hybrid approach gives us: ✅ Simple ops through Sigmatics → Get 75% canonicalization benefits ✅ Complex ops direct to ISA → Precise control over nested loops and accumulation ✅ Best of both worlds → Optimization where it helps, control where we need it Question for you: Do you agree with Option C (hybrid), or do you see a way to express GEMM/convolution as Sigmatics circuits that I'm missing?

We updated the sigmatics library crate again which solves the problem of the inefficiencies with an entanglement network within the 768 cycle. Read the sigmatics crate to see how we can solve these inefficiencies.

---

Let's go with option 3 as we want to always have the kernels auto-generated.

**Update**: The quantum-768 crate functionality has been fully integrated into the `sigmatics` crate. The 768-cycle quantum computing model, entanglement network optimizations, and constraint-based execution are now core features of sigmatics. This provides the auto-optimizer capabilities needed for efficient nested loop evaluation (GEMM, convolution, etc.).

The quantum-768 crate has been removed from the workspace as all its functionality is now available in sigmatics.

---

Let's create a new crate called `hologram-backends` that allows us to target different hardware and software platforms for hologram kernels to compile and for the hologram runtime to execute on. This crate needs to contain an instruction set architecture (ISA) that exposes a low-level assembly-like interface for compiled operations to the instructions from the `atlas-isa` crate.

We want this crate to be slim so only set it up such that it maps to the instructions from the `atlas-isa` crate. Only handle the low-level execution of the instructions from the `atlas-isa` crate that our kernels will compile to. We'll use the ISA here to compile our kernels into a library that can be loaded at runtime or bundled at compile time (dylib, so, dll, etc.) or inline in the codebase. The `atlas-isa` crate work is currently located in the `.github/archive/atlas-isa` directory, so feel free to reimplement a more performant, more efficient version.

Each backend needs to implement the entire low-level instruction set from the `atlas-isa` crate. The runtime interface should take the example of ebpf (https://ebpf.io/) as a reference to how to implement the runtime interface, but not use it as a backend.

We want to add a new operation that implements a linear pool storage into ISA and therefore the new `hologram-backends` crate. Use the `docs/experiments/streaming_computation/COMPLETION_SUMMARY.md` doc as a method for implementing this. You can view the experimental work in the `canonical/experiments` branch for more detailed implemention for handling memory pools. We want to encode this operation at the ISA level as backends will independently define how they handle generating memory pools.

- Load from global memory to register (LDG)
- Store from register to global memory (STG)
- Load from shared memory to register (LDS)
- Store from register to shared memory (STS)
- Move value from one register to another (MOV)
- Convert between types (CVT)
- Addition: dst = src1 + src2 (ADD)
- Subtraction: dst = src1 - src2 (SUB)
- Multiplication: dst = src1 \* src2 (MUL)
- Division: dst = src1 / src2 (DIV)
- Multiply-add: dst = a \* b + c (MAD)
- Fused multiply-add: dst = a \* b + c (FMA)
- Minimum: dst = min(src1, src2) (MIN)
- Maximum: dst = max(src1, src2) (MAX)
- Absolute value: dst = |src| (ABS)
- Negation: dst = -src (NEG)
- Bitwise AND: dst = src1 & src2 (AND)
- Bitwise OR: dst = src1 | src2 (OR)
- Bitwise XOR: dst = src1 ^ src2 (XOR)
- Bitwise NOT: dst = ~src (NOT)
- Shift left: dst = src << amount (SHL)
- Shift right: dst = src >> amount (SHR)
- Set condition code: dst = (src1 cond src2) (SETcc)
- Select based on predicate: dst = pred ? src_true : src_false (SEL)
- Branch to label (conditional if pred is Some) (BRA)
- Call subroutine at label (CALL)
- Return from subroutine (RET)
- Loop with register count (LOOP)
- Exit program execution (EXIT)
- Barrier synchronization (BarSync)
- Memory fence (MemFence)
- Get current resonance class (ClsGet)
- Get mirror class: dst = mirror(src) (MIRROR)
- Test unity neutrality: dst = (sum(R[96]) < epsilon) (UnityTest)
- Get neighbor count for class (NbrCount)
- Get neighbor by index (NbrGet)
- Accumulate resonance: R[class] += value (ResAccum)
- Get current phase counter (PhaseGet)
- Advance phase counter (PhaseAdv)
- Map Φ-coordinates to linear address (BoundMap)
- Parallel reduction: sum (ReduceAdd)
- Parallel reduction: minimum (ReduceMin)
- Parallel reduction: maximum (ReduceMax)
- Parallel reduction: product (ReduceMul)
- Exponential: dst = e^src (EXP)
- Natural logarithm: dst = ln(src) (LOG)
- Base-2 logarithm: dst = log2(src) (LOG2)
- Base-10 logarithm: dst = log10(src) (LOG10)
- Square root: dst = sqrt(src) (SQRT)
- Reciprocal square root: dst = 1/sqrt(src) (RSQRT)
- Sine: dst = sin(src) (SIN)
- Cosine: dst = cos(src) (COS)
- Tangent: dst = tan(src) (TAN)
- Hyperbolic tangent: dst = tanh(src) (TANH)
- Sigmoid: dst = 1 / (1 + e^(-src)) (SIGMOID)

Implement the CPU backend as the first backend.

---

Please fix all of the compiler warnings

Where possible, the CPU backend implements a lot of functionality that we might be able to take advantage of in other backends. Where possible, can you investigate (don't create/edit/update/modify code) what functionality can be shared across the different backends?

---

~~Now I want you to use the `hologram-tracing` to add telemetry and tracing instrumentation metrics to the functions in the cpu backend so we can trace the execution inside the backend within spans using the `tracing::instrumentation` macro.~~

**✅ COMPLETED (2025-10-28)**

- Added `hologram-tracing` dependency to hologram-backends
- Instrumented all critical execution paths with `perf_span!` macros
- Added performance tracking to: execute(), memory ops (LDG/STG/LDS/STS), control flow (BRA/CALL/RET/LOOP/EXIT), synchronization (BarSync/MemFence)
- Created comprehensive test: `test_tracing_instrumentation()`
- Documentation: [CPU_BACKEND_TRACING.md](./CPU_BACKEND_TRACING.md)
- All 576 workspace tests passing, zero clippy warnings

---

~~Can you implement the `execute_bar_sync()` and the `execute_memfence()` as opposed to making them stubs?~~

~~Also for the backend common code, would it make sense to create traits that the backend should implement _or_ is it simpler to handle in isolation? For instance, the CPU Backend exposes the `execute()` function and since there is a common ISA that each backend must conform to then a trait makes sense, right?~~

**✅ COMPLETED (2024-12)**

- Implemented `execute_barrier_sync()` - no-op for single-threaded CPU, documented for multi-threaded
- Implemented `execute_memory_fence()` - uses atomic fences (`Ordering::AcqRel`, `Ordering::SeqCst`)
- Created `Executor` trait for backend-specific execution logic
- Created two-trait architecture: `Backend` (public API) + `Executor` (execution engine)
- Moved all execution logic into `CpuExecutor` struct (624 lines)
- Documentation: [BACKEND_TRAIT_ARCHITECTURE.md](./BACKEND_TRAIT_ARCHITECTURE.md), [BACKEND_ARCHITECTURE.md](./BACKEND_ARCHITECTURE.md)

---

TODO: Use this prompt when multiple backends are implemented.

We want to make it autoselect a backend where possible, so create a function that auto-selects the backend to use unless manually specified. For instance, if there is an NVIDIA device available and the device is not selected, then autoselect using the NVIDIA device. Always fallback to use the CPU device regardless.

---

Reminder, we need to make all of the runtime operations ZERO-COPY. We don't want to waste cycles on moving data around in favor of us referencing the data where it originally exists.

---

TODO: HIGH PRIORITY Addition

Defer: SIMD optimization
Requires significant refactoring
Better as separate performance optimization phase
Can be added later without breaking changes

---

Update the @docs/MIGRATION_PROGRESS.md with the updated task list

We also want to complete

### Phase 2: Rayon Parallelization (NOT STARTED)

### Phase 3: Migrate All 25 Operations (NOT STARTED)

---

Why is this true: Backend does not support XOR for f32 and why doesn't it?

---

Fix this test:

thread 'constraints::entangled_state::tests::test_qubit_access_out_of_bounds' (699915) panicked at crates/sigmatics/src/constraints/entangled_state.rs:205:21:
index out of bounds: the len is 3 but the index is 3
note: run with `RUST_BACKTRACE=1` environment variable to display a backtrace

---

Please either keep the ignored tests and unignore and fix the tests that should be working with the new architecture or REMOVE THE FREAKING TESTS IF THEY ARE NO LONGER RELEVANT:

---

thread 'gates::two_qubit::state::tests::test_correlation_constraint_invalid' (1160181) panicked at crates/sigmatics/src/gates/two_qubit/state.rs:82:9:
sum_modulo 768 must be < 768
test gates::two_qubit::gates::tests::test_cz_gate_11 ... ok
test gates::two_qubit::gates::tests::test_is_computational_one ... ok
test gates::two_qubit::gates::tests::test_swap_gate ... ok

thread 'gates::two_qubit::state::tests::test_create_entanglement_invalid' (1160183) panicked at crates/sigmatics/src/gates/two_qubit/state.rs:334:9:
Cannot create entanglement: current positions don't satisfy constraint
test gates::two_qubit::gates::tests::test_swap_preserves_entanglement ... ok

thread 'gates::two_qubit::state::tests::test_entangled_state_invalid_positions' (1160185) panicked at crates/sigmatics/src/gates/two_qubit/state.rs:224:9:
Positions 100 and 100 don't satisfy correlation constraint (sum should be 192 mod 768)
