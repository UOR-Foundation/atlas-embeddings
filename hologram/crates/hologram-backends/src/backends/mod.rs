//! Backend implementations for different execution targets
//!
//! This module contains:
//! - `common` - Shared backend infrastructure (registers, memory, execution state, Atlas ops)
//! - `cpu` - CPU backend (reference implementation)
//! - `metal` - Metal GPU backend (Apple Silicon)
//! - `cuda` - CUDA GPU backend (NVIDIA GPUs)
//! - `tpu` - TPU backend via PJRT (TODO)
//! - `fpga` - FPGA backend (TODO)

pub mod common;
pub mod cpu;
pub mod cuda;
pub mod metal;

// Re-export backends
pub use cpu::CpuBackend;
pub use cuda::CudaBackend;
pub use metal::MetalBackend;
