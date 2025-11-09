//! Register Allocation
//!
//! Manages register assignment for compiled programs to minimize register usage.

use crate::{Error, Result};
use hologram_backends::{Predicate, Register};

/// Register allocator for efficient register assignment
///
/// Tracks which registers are in use and provides allocation/deallocation.
///
/// # Example
///
/// ```text
/// let mut allocator = RegisterAllocator::new();
///
/// // Allocate registers for temporaries
/// let r0 = allocator.alloc()?;  // R0
/// let r1 = allocator.alloc()?;  // R1
///
/// // Use registers...
///
/// // Free when done
/// allocator.free(r0);
/// allocator.free(r1);
///
/// // Can be reused
/// let r2 = allocator.alloc()?;  // R0 (reused)
/// ```
#[derive(Debug)]
pub struct RegisterAllocator {
    /// Next available register index
    next_reg: u8,

    /// Stack of freed registers (for reuse)
    free_list: Vec<u8>,

    /// Maximum register used (for debugging)
    max_used: u8,
}

impl RegisterAllocator {
    /// Create a new register allocator
    pub fn new() -> Self {
        Self {
            next_reg: 0,
            free_list: Vec::new(),
            max_used: 0,
        }
    }

    /// Create allocator starting at specific register
    ///
    /// Useful for reserving low registers for specific purposes
    pub fn with_start(start: u8) -> Self {
        Self {
            next_reg: start,
            free_list: Vec::new(),
            max_used: start,
        }
    }

    /// Allocate a new register
    ///
    /// Returns a free register, either from the free list or the next available.
    ///
    /// # Errors
    ///
    /// Returns error if all 256 registers are exhausted.
    pub fn alloc(&mut self) -> Result<Register> {
        // Try to reuse freed register first
        if let Some(reg_idx) = self.free_list.pop() {
            return Ok(Register::new(reg_idx));
        }

        // Allocate next register (check for overflow since next_reg is u8)
        let reg = Register::new(self.next_reg);
        self.next_reg = self
            .next_reg
            .checked_add(1)
            .ok_or_else(|| Error::InvalidOperation("Exhausted all 256 registers".to_string()))?;
        self.max_used = self.max_used.max(self.next_reg.saturating_sub(1));

        Ok(reg)
    }

    /// Allocate a block of consecutive registers
    ///
    /// Useful for vector operations that need adjacent registers.
    pub fn alloc_block(&mut self, count: u8) -> Result<Vec<Register>> {
        let mut regs = Vec::with_capacity(count as usize);
        for _ in 0..count {
            regs.push(self.alloc()?);
        }
        Ok(regs)
    }

    /// Free a register for reuse
    ///
    /// The register will be available for the next `alloc()` call.
    pub fn free(&mut self, reg: Register) {
        self.free_list.push(reg.index());
    }

    /// Free multiple registers
    pub fn free_all(&mut self, regs: impl IntoIterator<Item = Register>) {
        for reg in regs {
            self.free(reg);
        }
    }

    /// Reset allocator to initial state
    ///
    /// All registers become available again.
    pub fn reset(&mut self) {
        self.next_reg = 0;
        self.free_list.clear();
        self.max_used = 0;
    }

    /// Get maximum register index used
    ///
    /// Useful for debugging and optimization analysis.
    pub fn max_used(&self) -> u8 {
        self.max_used
    }

    /// Get number of currently allocated registers
    pub fn active_count(&self) -> usize {
        (self.next_reg as usize) - self.free_list.len()
    }
}

impl Default for RegisterAllocator {
    fn default() -> Self {
        Self::new()
    }
}

/// Predicate allocator for conditional operations
///
/// Manages the 16 predicate registers (P0-P15).
#[derive(Debug)]
pub struct PredicateAllocator {
    next_pred: u8,
    free_list: Vec<u8>,
}

impl PredicateAllocator {
    /// Create a new predicate allocator
    pub fn new() -> Self {
        Self {
            next_pred: 0,
            free_list: Vec::new(),
        }
    }

    /// Allocate a predicate register
    ///
    /// # Errors
    ///
    /// Returns error if all 16 predicates are exhausted.
    pub fn alloc(&mut self) -> Result<Predicate> {
        if let Some(pred_idx) = self.free_list.pop() {
            return Ok(Predicate::new(pred_idx));
        }

        if self.next_pred >= 16 {
            return Err(Error::InvalidOperation("Exhausted all 16 predicates".to_string()));
        }

        let pred = Predicate::new(self.next_pred);
        self.next_pred += 1;

        Ok(pred)
    }

    /// Free a predicate for reuse
    pub fn free(&mut self, pred: Predicate) {
        self.free_list.push(pred.index());
    }

    /// Reset allocator
    #[allow(dead_code)]
    pub fn reset(&mut self) {
        self.next_pred = 0;
        self.free_list.clear();
    }
}

impl Default for PredicateAllocator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_register_alloc() {
        let mut allocator = RegisterAllocator::new();

        let r0 = allocator.alloc().unwrap();
        let r1 = allocator.alloc().unwrap();
        let r2 = allocator.alloc().unwrap();

        assert_eq!(r0.index(), 0);
        assert_eq!(r1.index(), 1);
        assert_eq!(r2.index(), 2);
        assert_eq!(allocator.max_used(), 2);
    }

    #[test]
    fn test_register_reuse() {
        let mut allocator = RegisterAllocator::new();

        let r0 = allocator.alloc().unwrap();
        let _r1 = allocator.alloc().unwrap();

        allocator.free(r0);

        let r2 = allocator.alloc().unwrap();
        assert_eq!(r2.index(), 0); // Reused r0
    }

    #[test]
    fn test_register_block() {
        let mut allocator = RegisterAllocator::new();

        let block = allocator.alloc_block(4).unwrap();
        assert_eq!(block.len(), 4);
        assert_eq!(block[0].index(), 0);
        assert_eq!(block[3].index(), 3);
    }

    #[test]
    fn test_predicate_alloc() {
        let mut allocator = PredicateAllocator::new();

        let p0 = allocator.alloc().unwrap();
        let p1 = allocator.alloc().unwrap();

        assert_eq!(p0.index(), 0);
        assert_eq!(p1.index(), 1);
    }

    #[test]
    fn test_predicate_reuse() {
        let mut allocator = PredicateAllocator::new();

        let p0 = allocator.alloc().unwrap();
        allocator.free(p0);

        let p1 = allocator.alloc().unwrap();
        assert_eq!(p1.index(), 0); // Reused
    }

    #[test]
    fn test_with_start() {
        let mut allocator = RegisterAllocator::with_start(10);

        let r = allocator.alloc().unwrap();
        assert_eq!(r.index(), 10);
    }
}
