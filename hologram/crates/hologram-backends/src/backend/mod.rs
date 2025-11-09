//! Backend trait and types for kernel execution

mod traits;
mod types;

pub use traits::Backend;
pub use types::{BlockDim, BufferHandle, ExecutionContext, GridDim, LaunchConfig, PoolHandle, SharedMemoryConfig};
