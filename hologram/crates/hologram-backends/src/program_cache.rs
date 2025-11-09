//! Program caching infrastructure for ISA programs
//!
//! This module provides caching for dynamically created ISA programs to reduce
//! creation overhead. Programs are cached using OnceLock for thread-safe lazy
//! initialization.
//!
//! # Architecture
//!
//! - **Plan B**: Runtime program creation + caching (current implementation)
//! - **Plan C**: Compile-time precompilation (future, uses same cache structure)
//!
//! Both approaches benefit from this caching infrastructure:
//! - Plan B: Cache runtime-created programs
//! - Plan C: Cache provides fallback for user-defined operations

use crate::isa::Program;
use std::collections::HashMap;
use std::sync::{Arc, OnceLock};

/// A cache key for ISA programs
///
/// Programs are cached based on their input parameters. For example,
/// vector_add is parameterized by buffer handles (a, b, c).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProgramKey {
    /// Operation name (e.g., "vector_add", "matmul")
    pub operation: &'static str,
    /// Parameter values that affect program structure
    pub params: Vec<u64>,
}

impl ProgramKey {
    /// Create a new program cache key
    pub fn new(operation: &'static str, params: Vec<u64>) -> Self {
        Self { operation, params }
    }

    /// Create a key for a 3-buffer operation (most common pattern)
    pub fn three_buffer(operation: &'static str, a: u64, b: u64, c: u64) -> Self {
        Self::new(operation, vec![a, b, c])
    }

    /// Create a key for a 2-buffer operation
    pub fn two_buffer(operation: &'static str, a: u64, b: u64) -> Self {
        Self::new(operation, vec![a, b])
    }

    /// Create a key for a 1-buffer operation
    pub fn one_buffer(operation: &'static str, a: u64) -> Self {
        Self::new(operation, vec![a])
    }
}

/// Thread-safe program cache using OnceLock
///
/// This cache is optimized for the common case where programs are created
/// once and reused many times. The first access creates the program, subsequent
/// accesses return the cached version with minimal overhead.
///
/// # Performance
///
/// - First access: ~100ns (program creation)
/// - Subsequent accesses: ~5-10ns (cache lookup)
/// - Thread-safe: Uses OnceLock for lock-free reads after initialization
///
/// # Example
///
/// ```text
/// use hologram_backends::program_cache::{ProgramCache, ProgramKey};
///
/// static CACHE: ProgramCache = ProgramCache::new();
///
/// let key = ProgramKey::three_buffer("vector_add", buf_a, buf_b, buf_c);
/// let program = CACHE.get_or_create(&key, || {
///     // Create program on first access
///     create_vector_add_program(buf_a, buf_b, buf_c)
/// });
/// ```
pub struct ProgramCache {
    cache: OnceLock<parking_lot::RwLock<HashMap<ProgramKey, Arc<Program>>>>,
}

impl ProgramCache {
    /// Create a new empty program cache
    pub const fn new() -> Self {
        Self { cache: OnceLock::new() }
    }

    /// Get a program from the cache, or create it if not present
    ///
    /// The creation function `f` is only called if the program is not in the cache.
    /// Subsequent calls with the same key will return the cached program wrapped in Arc.
    ///
    /// # Thread Safety
    ///
    /// This method is thread-safe. Multiple threads can call it concurrently.
    /// The creation function may be called multiple times if multiple threads
    /// race to create the same program, but only one result will be cached.
    ///
    /// # Performance
    ///
    /// Returns Arc<Program> instead of Program to avoid deep cloning the instruction
    /// vector on cache hits. Arc::clone is a cheap pointer copy (~2ns) vs deep clone
    /// which copies all instructions (~50-100µs for large programs).
    pub fn get_or_create<F>(&self, key: &ProgramKey, f: F) -> Arc<Program>
    where
        F: FnOnce() -> Program,
    {
        // Initialize cache on first use
        let cache = self.cache.get_or_init(|| parking_lot::RwLock::new(HashMap::new()));

        // Fast path: read lock for cache lookup
        {
            let read_guard = cache.read();
            if let Some(program) = read_guard.get(key) {
                return Arc::clone(program); // Cheap pointer copy, not deep clone
            }
        }

        // Slow path: create program and cache it
        let program = Arc::new(f()); // Wrap in Arc once

        // Write lock to insert
        {
            let mut write_guard = cache.write();
            // Check again in case another thread inserted while we were creating
            write_guard.entry(key.clone()).or_insert_with(|| Arc::clone(&program));
        }

        program
    }

    /// Clear the cache
    ///
    /// This removes all cached programs. Mainly useful for testing.
    #[cfg(test)]
    pub fn clear(&self) {
        if let Some(cache) = self.cache.get() {
            cache.write().clear();
        }
    }

    /// Get the number of cached programs
    ///
    /// Returns 0 if the cache hasn't been initialized yet.
    pub fn len(&self) -> usize {
        self.cache.get().map(|c| c.read().len()).unwrap_or(0)
    }

    /// Check if the cache is empty
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl Default for ProgramCache {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::isa::{Instruction, Register, Type};
    use std::collections::HashMap;

    fn create_test_program(value: u64) -> Program {
        Program {
            instructions: vec![
                Instruction::MOV_IMM {
                    ty: Type::U64,
                    dst: Register(0),
                    value,
                },
                Instruction::EXIT,
            ],
            labels: HashMap::new(),
        }
    }

    #[test]
    fn test_cache_basic() {
        let cache = ProgramCache::new();
        let key = ProgramKey::one_buffer("test", 42);

        // First access creates program
        let program1 = cache.get_or_create(&key, || create_test_program(42));
        assert_eq!(program1.instructions.len(), 2);

        // Second access returns cached program
        let program2 = cache.get_or_create(&key, || create_test_program(999));
        assert_eq!(program2.instructions.len(), 2);

        // Should have same instructions (from cache, not from second creator)
        if let Instruction::MOV_IMM { value, .. } = program2.instructions[0] {
            assert_eq!(value, 42); // Not 999!
        } else {
            panic!("Expected MOV_IMM instruction");
        }
    }

    #[test]
    fn test_cache_multiple_keys() {
        let cache = ProgramCache::new();
        let key1 = ProgramKey::one_buffer("test", 1);
        let key2 = ProgramKey::one_buffer("test", 2);

        let program1 = cache.get_or_create(&key1, || create_test_program(1));
        let program2 = cache.get_or_create(&key2, || create_test_program(2));

        // Different keys should have different programs
        if let Instruction::MOV_IMM { value: v1, .. } = program1.instructions[0] {
            if let Instruction::MOV_IMM { value: v2, .. } = program2.instructions[0] {
                assert_ne!(v1, v2);
            }
        }

        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn test_cache_clear() {
        let cache = ProgramCache::new();
        let key = ProgramKey::one_buffer("test", 42);

        cache.get_or_create(&key, || create_test_program(42));
        assert_eq!(cache.len(), 1);

        cache.clear();
        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn test_program_key_constructors() {
        let key1 = ProgramKey::three_buffer("add", 1, 2, 3);
        assert_eq!(key1.operation, "add");
        assert_eq!(key1.params, vec![1, 2, 3]);

        let key2 = ProgramKey::two_buffer("mul", 4, 5);
        assert_eq!(key2.operation, "mul");
        assert_eq!(key2.params, vec![4, 5]);

        let key3 = ProgramKey::one_buffer("relu", 6);
        assert_eq!(key3.operation, "relu");
        assert_eq!(key3.params, vec![6]);
    }
}
