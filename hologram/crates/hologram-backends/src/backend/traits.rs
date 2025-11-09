//! Backend trait for kernel execution
//!
//! This trait defines the interface that all backends must implement.
//! Backends execute programs defined in the Atlas ISA on various hardware targets.

use super::types::{BufferHandle, LaunchConfig, PoolHandle};
use crate::error::Result;
use crate::isa::Program;

/// Backend trait for kernel execution
///
/// Backends implement this trait to provide execution of Atlas ISA programs
/// on different hardware targets (CPU, GPU, TPU, FPGA, etc.).
///
/// # Architecture
///
/// ```text
/// ┌─────────────────────────────────────────────────────────┐
/// │                     Backend Trait                        │
/// │  - execute_program()                                     │
/// │  - Buffer management (allocate/free/copy)                │
/// │  - Pool management (allocate/free)                       │
/// └─────────────────────┬───────────────────────────────────┘
///                       │
///         ┌─────────────┼─────────────┬─────────────┐
///         ▼             ▼             ▼             ▼
///   ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐
///   │   CPU   │  │   GPU   │  │   TPU   │  │  FPGA   │
///   │ Backend │  │ Backend │  │ Backend │  │ Backend │
///   └─────────┘  └─────────┘  └─────────┘  └─────────┘
/// ```
///
/// # Memory Model
///
/// Backends manage two types of memory:
///
/// 1. **Buffers** - General-purpose linear memory
///    - Allocated via `allocate_buffer()`
///    - Accessed via LDG/STG instructions
///    - Used for input/output data
///
/// 2. **Pools** - Linear pool storage (O(1) space streaming)
///    - Allocated via `allocate_pool()`
///    - Accessed via PoolLoad/PoolStore instructions
///    - Enables streaming computation with fixed memory
///
/// # Usage
///
/// ```rust
/// use hologram_backends::{CpuBackend, Backend, Program, Instruction, Register, Type, Address};
///
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// let mut backend = CpuBackend::new();
///
/// // Allocate buffer
/// let buffer = backend.allocate_buffer(1024)?;
///
/// // Write data to buffer
/// let data = vec![1.0f32, 2.0, 3.0, 4.0];
/// backend.copy_to_buffer(buffer, bytemuck::cast_slice(&data))?;
///
/// // Create and execute program
/// let mut program = Program::new();
/// // Load value from buffer into register 1
/// program.instructions.push(Instruction::LDG {
///     ty: Type::F32,
///     dst: Register::new(1),
///     addr: Address::BufferOffset { handle: buffer.id(), offset: 0 },
/// });
/// // Move from register 1 to register 0
/// program.instructions.push(Instruction::MOV {
///     ty: Type::F32,
///     dst: Register::new(0),
///     src: Register::new(1),
/// });
/// // Store result back to buffer
/// program.instructions.push(Instruction::STG {
///     ty: Type::F32,
///     src: Register::new(0),
///     addr: Address::BufferOffset { handle: buffer.id(), offset: 16 },
/// });
///
/// let config = Default::default();
/// backend.execute_program(&program, &config)?;
///
/// // Read results
/// let mut results = vec![0.0f32; 4];
/// backend.copy_from_buffer(buffer, bytemuck::cast_slice_mut(&mut results))?;
///
/// backend.free_buffer(buffer)?;
/// # Ok(())
/// # }
/// ```
///
/// # Pool Storage Example
///
/// ```rust
/// use hologram_backends::{CpuBackend, Backend};
///
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// let mut backend = CpuBackend::new();
///
/// // Allocate fixed-size pool
/// let pool = backend.allocate_pool(4096)?;
///
/// // Stream large data through fixed pool
/// let large_data = vec![0.0f32; 1_000_000];
/// for chunk in large_data.chunks(1024) {
///     // Load chunk into pool
///     backend.copy_to_pool(pool, 0, bytemuck::cast_slice(chunk))?;
///
///     // Execute operations on pool
///     // backend.execute_program(&program, &config)?;
///
///     // Read results from pool
///     // backend.copy_from_pool(pool, 0, &mut results)?;
/// }
///
/// backend.free_pool(pool)?;
/// # Ok(())
/// # }
/// ```
pub trait Backend {
    // ============================================================================================
    // Program Execution
    // ============================================================================================

    /// Execute a program with the given launch configuration
    ///
    /// # Arguments
    ///
    /// * `program` - The program to execute (sequence of Atlas ISA instructions)
    /// * `config` - Launch configuration (grid/block dimensions, shared memory)
    ///
    /// # Execution Model
    ///
    /// The backend executes the program across a grid of blocks:
    ///
    /// ```text
    /// Grid (config.grid):
    ///   ┌─────┬─────┬─────┐
    ///   │Block│Block│Block│  Each block contains...
    ///   ├─────┼─────┼─────┤
    ///   │Block│Block│Block│
    ///   └─────┴─────┴─────┘
    ///
    /// Block (config.block):
    ///   ┌────┬────┬────┐
    ///   │Lane│Lane│Lane│  Each lane executes the program
    ///   ├────┼────┼────┤
    ///   │Lane│Lane│Lane│
    ///   └────┴────┴────┘
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Program contains invalid instructions
    /// - Control flow labels are undefined
    /// - Memory access is out of bounds
    /// - Type errors occur during execution
    fn execute_program(&mut self, program: &Program, config: &LaunchConfig) -> Result<()>;

    // ============================================================================================
    // Buffer Management
    // ============================================================================================

    /// Allocate a buffer of the given size in bytes
    ///
    /// Returns a handle to the allocated buffer. The handle can be used in
    /// Address::BufferOffset for LDG/STG instructions.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use hologram_backends::{CpuBackend, Backend};
    /// # let mut backend = CpuBackend::new();
    /// let buffer = backend.allocate_buffer(1024)?;
    /// // Use buffer in program...
    /// backend.free_buffer(buffer)?;
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn allocate_buffer(&mut self, size: usize) -> Result<BufferHandle>;

    /// Free a previously allocated buffer
    ///
    /// # Errors
    ///
    /// Returns an error if the buffer handle is invalid.
    fn free_buffer(&mut self, handle: BufferHandle) -> Result<()>;

    /// Copy data from host to buffer
    ///
    /// # Arguments
    ///
    /// * `handle` - Buffer handle
    /// * `data` - Data to copy
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Buffer handle is invalid
    /// - Data size exceeds buffer size
    fn copy_to_buffer(&mut self, handle: BufferHandle, data: &[u8]) -> Result<()>;

    /// Copy data from buffer to host
    ///
    /// # Arguments
    ///
    /// * `handle` - Buffer handle
    /// * `data` - Destination buffer
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Buffer handle is invalid
    /// - Data size exceeds buffer size
    fn copy_from_buffer(&mut self, handle: BufferHandle, data: &mut [u8]) -> Result<()>;

    /// Get buffer size in bytes
    ///
    /// # Errors
    ///
    /// Returns an error if the buffer handle is invalid.
    fn buffer_size(&self, handle: BufferHandle) -> Result<usize>;

    // ============================================================================================
    // Pool Storage Management
    // ============================================================================================

    /// Allocate a linear pool of the given size in bytes
    ///
    /// Pools enable O(1) space streaming computation. The pool can be reused
    /// for arbitrary input sizes by loading data in chunks.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use hologram_backends::{CpuBackend, Backend};
    /// # let mut backend = CpuBackend::new();
    /// // Allocate 36 KB pool (96 classes × 48 pages × 8 bytes)
    /// let pool = backend.allocate_pool(36_864)?;
    ///
    /// // Stream 100 MB through fixed 36 KB pool
    /// let large_data = vec![0.0f32; 25_000_000]; // 100 MB
    /// for chunk in large_data.chunks(9_216) { // 36 KB chunks
    ///     backend.copy_to_pool(pool, 0, bytemuck::cast_slice(chunk))?;
    ///     // Execute operations...
    ///     // backend.execute_program(&program, &config)?;
    /// }
    ///
    /// backend.free_pool(pool)?;
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    fn allocate_pool(&mut self, size: usize) -> Result<PoolHandle>;

    /// Free a previously allocated pool
    ///
    /// # Errors
    ///
    /// Returns an error if the pool handle is invalid.
    fn free_pool(&mut self, handle: PoolHandle) -> Result<()>;

    /// Copy data from host to pool
    ///
    /// # Arguments
    ///
    /// * `handle` - Pool handle
    /// * `offset` - Byte offset within pool
    /// * `data` - Data to copy
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Pool handle is invalid
    /// - Offset + data size exceeds pool size
    fn copy_to_pool(&mut self, handle: PoolHandle, offset: usize, data: &[u8]) -> Result<()>;

    /// Copy data from pool to host
    ///
    /// # Arguments
    ///
    /// * `handle` - Pool handle
    /// * `offset` - Byte offset within pool
    /// * `data` - Destination buffer
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Pool handle is invalid
    /// - Offset + data size exceeds pool size
    fn copy_from_pool(&mut self, handle: PoolHandle, offset: usize, data: &mut [u8]) -> Result<()>;

    /// Get pool size in bytes
    ///
    /// # Errors
    ///
    /// Returns an error if the pool handle is invalid.
    fn pool_size(&self, handle: PoolHandle) -> Result<usize>;

    // ============================================================================================
    // Type Introspection (for inline kernel fast paths)
    // ============================================================================================

    /// Downcast backend to &dyn Any for type-specific access
    ///
    /// This enables downcasting to concrete backend types (e.g., CpuBackend)
    /// for accessing backend-specific fast paths like inline SIMD kernels.
    fn as_any(&self) -> &dyn std::any::Any;

    /// Downcast backend to &mut dyn Any for type-specific access
    ///
    /// This enables downcasting to concrete backend types (e.g., CpuBackend)
    /// for accessing backend-specific mutable fast paths.
    fn as_any_mut(&mut self) -> &mut dyn std::any::Any;
}
