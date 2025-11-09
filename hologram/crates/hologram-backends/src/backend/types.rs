//! Types for backend configuration and handles

use std::fmt;

/// Handle to an allocated buffer
///
/// Buffers are opaque handles managed by the backend.
/// Use Backend methods to interact with buffers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BufferHandle(pub u64);

impl BufferHandle {
    /// Create a new buffer handle
    pub const fn new(id: u64) -> Self {
        BufferHandle(id)
    }

    /// Get the internal ID
    pub const fn id(self) -> u64 {
        self.0
    }
}

impl fmt::Display for BufferHandle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "buf{}", self.0)
    }
}

/// Handle to an allocated linear pool
///
/// Pools are opaque handles managed by the backend.
/// Use Backend methods to interact with pools.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PoolHandle(pub u64);

impl PoolHandle {
    /// Create a new pool handle
    pub const fn new(id: u64) -> Self {
        PoolHandle(id)
    }

    /// Get the internal ID
    pub const fn id(self) -> u64 {
        self.0
    }
}

impl fmt::Display for PoolHandle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "pool{}", self.0)
    }
}

/// Grid dimensions for kernel launch
///
/// Defines the 3D iteration space of blocks that execute the kernel.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GridDim {
    pub x: u32,
    pub y: u32,
    pub z: u32,
}

impl GridDim {
    /// Create new grid dimensions
    pub const fn new(x: u32, y: u32, z: u32) -> Self {
        Self { x, y, z }
    }

    /// Create 1D grid
    pub const fn linear(size: u32) -> Self {
        Self { x: size, y: 1, z: 1 }
    }

    /// Create 2D grid
    pub const fn square(x: u32, y: u32) -> Self {
        Self { x, y, z: 1 }
    }

    /// Get total number of blocks
    pub const fn total_blocks(&self) -> u64 {
        self.x as u64 * self.y as u64 * self.z as u64
    }
}

impl Default for GridDim {
    fn default() -> Self {
        Self { x: 1, y: 1, z: 1 }
    }
}

impl fmt::Display for GridDim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {}, {})", self.x, self.y, self.z)
    }
}

/// Block dimensions
///
/// Defines the 3D arrangement of lanes within a block.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BlockDim {
    pub x: u32,
    pub y: u32,
    pub z: u32,
}

impl BlockDim {
    /// Create new block dimensions
    pub const fn new(x: u32, y: u32, z: u32) -> Self {
        Self { x, y, z }
    }

    /// Create 1D block
    pub const fn linear(size: u32) -> Self {
        Self { x: size, y: 1, z: 1 }
    }

    /// Create 2D block
    pub const fn square(x: u32, y: u32) -> Self {
        Self { x, y, z: 1 }
    }

    /// Get total number of lanes per block
    pub const fn total_lanes(&self) -> u32 {
        self.x * self.y * self.z
    }
}

impl Default for BlockDim {
    fn default() -> Self {
        Self { x: 1, y: 1, z: 1 }
    }
}

impl fmt::Display for BlockDim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {}, {})", self.x, self.y, self.z)
    }
}

/// Shared memory configuration
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SharedMemoryConfig {
    /// Size of shared memory per block in bytes
    pub size_bytes: usize,
}

impl SharedMemoryConfig {
    /// Create new shared memory configuration
    pub const fn new(size_bytes: usize) -> Self {
        Self { size_bytes }
    }

    /// No shared memory
    pub const fn none() -> Self {
        Self { size_bytes: 0 }
    }
}

impl Default for SharedMemoryConfig {
    fn default() -> Self {
        Self::none()
    }
}

/// Launch configuration for kernel execution
///
/// Specifies the iteration space (grid × block) and resources required.
#[derive(Debug, Clone, Copy, Default)]
pub struct LaunchConfig {
    /// Grid dimensions (number of blocks in each dimension)
    pub grid: GridDim,

    /// Block dimensions (number of lanes per block in each dimension)
    pub block: BlockDim,

    /// Shared memory configuration
    pub shared_memory: SharedMemoryConfig,
}

impl LaunchConfig {
    /// Create new launch configuration
    pub const fn new(grid: GridDim, block: BlockDim, shared_memory: SharedMemoryConfig) -> Self {
        Self {
            grid,
            block,
            shared_memory,
        }
    }

    /// Create simple 1D launch configuration
    pub const fn linear(total_elements: u32, block_size: u32) -> Self {
        let num_blocks = total_elements.div_ceil(block_size);
        Self {
            grid: GridDim::linear(num_blocks),
            block: BlockDim::linear(block_size),
            shared_memory: SharedMemoryConfig::none(),
        }
    }

    /// Get total number of blocks
    pub const fn total_blocks(&self) -> u64 {
        self.grid.total_blocks()
    }

    /// Get total number of lanes across all blocks
    pub const fn total_lanes(&self) -> u64 {
        self.grid.total_blocks() * self.block.total_lanes() as u64
    }
}

impl fmt::Display for LaunchConfig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "grid={}, block={}, shared_mem={}B",
            self.grid, self.block, self.shared_memory.size_bytes
        )
    }
}

/// Execution context for a single lane
///
/// Provides positional information for lane execution.
#[derive(Debug, Clone, Copy)]
pub struct ExecutionContext {
    /// Block index within grid
    pub block_idx: (u32, u32, u32),

    /// Lane index within block
    pub lane_idx: (u32, u32, u32),

    /// Grid dimensions
    pub grid_dim: GridDim,

    /// Block dimensions
    pub block_dim: BlockDim,
}

impl ExecutionContext {
    /// Create new execution context
    pub const fn new(
        block_idx: (u32, u32, u32),
        lane_idx: (u32, u32, u32),
        grid_dim: GridDim,
        block_dim: BlockDim,
    ) -> Self {
        Self {
            block_idx,
            lane_idx,
            grid_dim,
            block_dim,
        }
    }

    /// Get linear block index
    pub const fn block_linear_index(&self) -> u64 {
        let (bx, by, bz) = self.block_idx;
        (bz as u64 * self.grid_dim.y as u64 * self.grid_dim.x as u64) + (by as u64 * self.grid_dim.x as u64) + bx as u64
    }

    /// Get linear lane index within block
    pub const fn lane_linear_index(&self) -> u32 {
        let (tx, ty, tz) = self.lane_idx;
        (tz * self.block_dim.y * self.block_dim.x) + (ty * self.block_dim.x) + tx
    }

    /// Get global linear lane index
    pub const fn global_lane_index(&self) -> u64 {
        self.block_linear_index() * self.block_dim.total_lanes() as u64 + self.lane_linear_index() as u64
    }

    /// Get resonance class from block X coordinate (Atlas convention)
    ///
    /// Maps the block to one of 96 resonance classes: `class_id = blockIdx.x mod 96`
    pub const fn resonance_class(&self) -> u8 {
        (self.block_idx.0 % 96) as u8
    }

    /// Get boundary coordinates from lane index (Atlas convention)
    ///
    /// Maps lane position to boundary lens coordinates:
    /// - `page = laneIdx.x mod 48`
    /// - `byte = laneIdx.y mod 256`
    pub const fn boundary_coords(&self) -> (u8, u8) {
        let page = (self.lane_idx.0 % 48) as u8;
        let byte = (self.lane_idx.1 % 256) as u8;
        (page, byte)
    }
}

// ================================================================================================
// Tests
// ================================================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_buffer_handle() {
        let handle = BufferHandle::new(42);
        assert_eq!(handle.id(), 42);
        assert_eq!(handle.to_string(), "buf42");
    }

    #[test]
    fn test_pool_handle() {
        let handle = PoolHandle::new(7);
        assert_eq!(handle.id(), 7);
        assert_eq!(handle.to_string(), "pool7");
    }

    #[test]
    fn test_grid_dim() {
        let grid = GridDim::new(2, 3, 4);
        assert_eq!(grid.total_blocks(), 24);
        assert_eq!(grid.to_string(), "(2, 3, 4)");

        let linear = GridDim::linear(10);
        assert_eq!(linear.total_blocks(), 10);

        let square = GridDim::square(4, 4);
        assert_eq!(square.total_blocks(), 16);
    }

    #[test]
    fn test_block_dim() {
        let block = BlockDim::new(8, 8, 1);
        assert_eq!(block.total_lanes(), 64);
        assert_eq!(block.to_string(), "(8, 8, 1)");

        let linear = BlockDim::linear(256);
        assert_eq!(linear.total_lanes(), 256);

        let square = BlockDim::square(16, 16);
        assert_eq!(square.total_lanes(), 256);
    }

    #[test]
    fn test_launch_config() {
        let config = LaunchConfig::new(
            GridDim::new(2, 2, 1),
            BlockDim::new(8, 8, 1),
            SharedMemoryConfig::new(1024),
        );

        assert_eq!(config.total_blocks(), 4);
        assert_eq!(config.total_lanes(), 256); // 4 blocks * 64 lanes/block

        let linear = LaunchConfig::linear(1000, 256);
        assert_eq!(linear.grid.x, 4); // ceil(1000 / 256)
        assert_eq!(linear.block.x, 256);
        assert_eq!(linear.shared_memory.size_bytes, 0);
    }

    #[test]
    fn test_execution_context() {
        let ctx = ExecutionContext::new((1, 2, 0), (5, 10, 0), GridDim::new(4, 4, 2), BlockDim::new(8, 8, 1));

        assert_eq!(ctx.block_linear_index(), 9); // 0*4*4 + 2*4 + 1
        assert_eq!(ctx.lane_linear_index(), 85); // 0*8*8 + 10*8 + 5
        assert_eq!(ctx.global_lane_index(), 9 * 64 + 85);
    }

    #[test]
    fn test_execution_context_resonance_class() {
        let ctx = ExecutionContext::new((100, 0, 0), (0, 0, 0), GridDim::new(200, 1, 1), BlockDim::new(1, 1, 1));

        assert_eq!(ctx.resonance_class(), 4); // 100 % 96
    }

    #[test]
    fn test_execution_context_boundary_coords() {
        let ctx = ExecutionContext::new(
            (0, 0, 0),
            (50, 300, 0),
            GridDim::new(1, 1, 1),
            BlockDim::new(100, 400, 1),
        );

        let (page, byte) = ctx.boundary_coords();
        assert_eq!(page, 2); // 50 % 48
        assert_eq!(byte, 44); // 300 % 256
    }
}
