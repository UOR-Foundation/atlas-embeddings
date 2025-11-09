//! Metal executor for Atlas ISA program execution
//!
//! Analyzes Atlas ISA programs and dispatches compatible operations to Metal GPU kernels.

#[cfg(target_vendor = "apple")]
use super::memory::MetalMemoryManager;
#[cfg(target_vendor = "apple")]
use super::pipeline::PipelineCache;
#[cfg(target_vendor = "apple")]
use crate::backend::LaunchConfig;
#[cfg(target_vendor = "apple")]
use crate::error::{BackendError, Result};
#[cfg(target_vendor = "apple")]
use crate::isa::{Address, Instruction, Program, Register, Type};

#[cfg(target_vendor = "apple")]
use metal::{CommandQueue, MTLSize};
#[cfg(target_vendor = "apple")]
use parking_lot::RwLock;
#[cfg(target_vendor = "apple")]
use std::sync::Arc;

/// Pattern for simple element-wise binary operations
#[cfg(target_vendor = "apple")]
#[derive(Debug)]
struct ElementWiseBinaryPattern {
    /// Operation type (ADD, SUB, MUL, DIV, MIN, MAX)
    op_type: ElementWiseOp,

    /// Data type (F32, I32)
    ty: Type,

    /// Input buffer A handle
    buffer_a: u64,

    /// Input buffer B handle
    buffer_b: u64,

    /// Output buffer C handle
    buffer_c: u64,

    /// Number of elements
    n: usize,
}

#[cfg(target_vendor = "apple")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ElementWiseOp {
    Add,
    Sub,
    Mul,
    Div,
    Min,
    Max,
    Abs,
    Neg,
    Sqrt,
    Exp,
    Log,
    Sigmoid,
    Tanh,
    Relu,
}

#[cfg(target_vendor = "apple")]
impl ElementWiseOp {
    /// Get Metal kernel name for this operation and type
    fn kernel_name(&self, ty: Type) -> Option<String> {
        let type_suffix = match ty {
            Type::F32 => "f32",
            Type::I32 => "i32",
            _ => return None, // Only support f32 and i32 for now
        };

        let op_name = match self {
            Self::Add => "add",
            Self::Sub => "sub",
            Self::Mul => "mul",
            Self::Div => "div",
            Self::Min => "min",
            Self::Max => "max",
            Self::Abs => "abs",
            Self::Neg => "neg",
            Self::Sqrt => "sqrt",
            Self::Exp => "exp",
            Self::Log => "log",
            Self::Sigmoid => "sigmoid",
            Self::Tanh => "tanh",
            Self::Relu => "relu",
        };

        // Check if this combination is supported
        match (self, ty) {
            // Float32 supports all operations
            (_, Type::F32) => Some(format!("atlas_{}_{}", op_name, type_suffix)),

            // Int32 only supports basic arithmetic
            (Self::Add | Self::Sub | Self::Mul | Self::Div, Type::I32) => {
                Some(format!("atlas_{}_{}", op_name, type_suffix))
            }

            // Other combinations not supported
            _ => None,
        }
    }

    /// Check if this is a unary operation
    fn is_unary(&self) -> bool {
        matches!(
            self,
            Self::Abs | Self::Neg | Self::Sqrt | Self::Exp | Self::Log | Self::Sigmoid | Self::Tanh | Self::Relu
        )
    }
}

/// Metal program executor
#[cfg(target_vendor = "apple")]
pub struct MetalExecutor {
    /// Command queue for GPU work submission
    command_queue: CommandQueue,

    /// Memory manager
    memory: Arc<RwLock<MetalMemoryManager>>,

    /// Pipeline cache
    pipeline_cache: Arc<RwLock<PipelineCache>>,
}

#[cfg(target_vendor = "apple")]
impl MetalExecutor {
    /// Create a new Metal executor
    pub fn new(
        command_queue: CommandQueue,
        memory: Arc<RwLock<MetalMemoryManager>>,
        pipeline_cache: Arc<RwLock<PipelineCache>>,
    ) -> Self {
        Self {
            command_queue,
            memory,
            pipeline_cache,
        }
    }

    /// Execute an Atlas ISA program on Metal GPU
    ///
    /// Currently supports simple element-wise operations. Complex control flow
    /// and other operations return UnsupportedOperation error.
    pub fn execute(&self, program: &Program, _config: &LaunchConfig) -> Result<()> {
        // Try to recognize as element-wise binary operation
        if let Some(pattern) = self.try_recognize_elementwise_binary(program)? {
            return self.execute_elementwise_binary(&pattern);
        }

        // Try to recognize as element-wise unary operation
        if let Some(pattern) = self.try_recognize_elementwise_unary(program)? {
            return self.execute_elementwise_unary(&pattern);
        }

        // Program pattern not recognized - not yet supported
        Err(BackendError::UnsupportedOperation(
            "Metal backend currently only supports simple element-wise operations. \
             Complex control flow and other operations not yet implemented."
                .into(),
        ))
    }

    /// Try to recognize program as element-wise binary operation pattern
    ///
    /// Pattern: Simple straight-line code with LDG → OP → STG
    /// Looks for:
    ///   LDG.ty r1, [bufA + offset]
    ///   LDG.ty r2, [bufB + offset]
    ///   OP.ty r3, r1, r2
    ///   STG.ty r3, [bufC + offset]
    fn try_recognize_elementwise_binary(&self, program: &Program) -> Result<Option<ElementWiseBinaryPattern>> {
        // Scan for binary arithmetic operations
        for (idx, instr) in program.instructions.iter().enumerate() {
            if let Some((op_type, ty, src1_reg, src2_reg, dst_reg)) = match instr {
                Instruction::ADD { ty, dst, src1, src2 } => Some((ElementWiseOp::Add, *ty, *src1, *src2, *dst)),
                Instruction::SUB { ty, dst, src1, src2 } => Some((ElementWiseOp::Sub, *ty, *src1, *src2, *dst)),
                Instruction::MUL { ty, dst, src1, src2 } => Some((ElementWiseOp::Mul, *ty, *src1, *src2, *dst)),
                Instruction::DIV { ty, dst, src1, src2 } => Some((ElementWiseOp::Div, *ty, *src1, *src2, *dst)),
                Instruction::MIN { ty, dst, src1, src2 } => Some((ElementWiseOp::Min, *ty, *src1, *src2, *dst)),
                Instruction::MAX { ty, dst, src1, src2 } => Some((ElementWiseOp::Max, *ty, *src1, *src2, *dst)),
                _ => None,
            } {
                // Found binary operation - now look for surrounding LDG/STG instructions
                // Try to find pattern: LDG r1, [bufA]; LDG r2, [bufB]; OP r3, r1, r2; STG r3, [bufC]

                let mut buffer_a = None;
                let mut buffer_b = None;
                let mut buffer_c = None;

                // Scan backwards for LDG instructions that load into src1_reg and src2_reg
                for prev_instr in program.instructions[..idx].iter().rev().take(10) {
                    if let Instruction::LDG { addr, dst, .. } = prev_instr {
                        if *dst == src1_reg && buffer_a.is_none() {
                            if let Address::BufferOffset { handle, .. } = addr {
                                buffer_a = Some(*handle);
                            }
                        }
                        if *dst == src2_reg && buffer_b.is_none() {
                            if let Address::BufferOffset { handle, .. } = addr {
                                buffer_b = Some(*handle);
                            }
                        }
                    }
                }

                // Scan forwards for STG instruction that stores from dst_reg
                for next_instr in program.instructions[(idx + 1)..].iter().take(10) {
                    if let Instruction::STG { addr, src, .. } = next_instr {
                        if *src == dst_reg && buffer_c.is_none() {
                            if let Address::BufferOffset { handle, .. } = addr {
                                buffer_c = Some(*handle);
                            }
                        }
                    }
                }

                // If we found all buffers, we have a match!
                if let (Some(buf_a), Some(buf_b), Some(buf_c)) = (buffer_a, buffer_b, buffer_c) {
                    // Estimate element count - for now, use a heuristic
                    // In a full implementation, we'd extract this from loop bounds or launch config
                    // For testing, assume reasonably sized buffers
                    let n = 1024; // TODO: Extract from program analysis or launch config

                    return Ok(Some(ElementWiseBinaryPattern {
                        op_type,
                        ty,
                        buffer_a: buf_a,
                        buffer_b: buf_b,
                        buffer_c: buf_c,
                        n,
                    }));
                }
            }
        }

        Ok(None)
    }

    /// Try to recognize program as element-wise unary operation pattern
    ///
    /// Pattern: Simple straight-line code with LDG → OP → STG
    /// Looks for:
    ///   LDG.ty r1, [bufA + offset]
    ///   OP.ty r2, r1
    ///   STG.ty r2, [bufB + offset]
    fn try_recognize_elementwise_unary(&self, program: &Program) -> Result<Option<ElementWiseBinaryPattern>> {
        // Scan for unary operations
        for (idx, instr) in program.instructions.iter().enumerate() {
            if let Some((op_type, ty, src_reg, dst_reg)) = match instr {
                Instruction::ABS { ty, dst, src } => Some((ElementWiseOp::Abs, *ty, *src, *dst)),
                Instruction::NEG { ty, dst, src } => Some((ElementWiseOp::Neg, *ty, *src, *dst)),
                Instruction::SQRT { ty, dst, src } => Some((ElementWiseOp::Sqrt, *ty, *src, *dst)),
                Instruction::EXP { ty, dst, src } => Some((ElementWiseOp::Exp, *ty, *src, *dst)),
                Instruction::LOG { ty, dst, src } => Some((ElementWiseOp::Log, *ty, *src, *dst)),
                Instruction::SIGMOID { ty, dst, src } => Some((ElementWiseOp::Sigmoid, *ty, *src, *dst)),
                Instruction::TANH { ty, dst, src } => Some((ElementWiseOp::Tanh, *ty, *src, *dst)),
                _ => None,
            } {
                // Found unary operation - look for surrounding LDG/STG
                let mut buffer_a = None;
                let mut buffer_b = None;

                // Scan backwards for LDG instruction that loads into src_reg
                for prev_instr in program.instructions[..idx].iter().rev().take(10) {
                    if let Instruction::LDG { addr, dst, .. } = prev_instr {
                        if *dst == src_reg && buffer_a.is_none() {
                            if let Address::BufferOffset { handle, .. } = addr {
                                buffer_a = Some(*handle);
                            }
                        }
                    }
                }

                // Scan forwards for STG instruction that stores from dst_reg
                for next_instr in program.instructions[(idx + 1)..].iter().take(10) {
                    if let Instruction::STG { addr, src, .. } = next_instr {
                        if *src == dst_reg && buffer_b.is_none() {
                            if let Address::BufferOffset { handle, .. } = addr {
                                buffer_b = Some(*handle);
                            }
                        }
                    }
                }

                // If we found both buffers, we have a match!
                if let (Some(buf_a), Some(buf_b)) = (buffer_a, buffer_b) {
                    let n = 1024; // TODO: Extract from program analysis

                    // Reuse ElementWiseBinaryPattern structure (buffer_b unused for unary)
                    return Ok(Some(ElementWiseBinaryPattern {
                        op_type,
                        ty,
                        buffer_a: buf_a,
                        buffer_b: 0, // Unused for unary ops
                        buffer_c: buf_b,
                        n,
                    }));
                }
            }
        }

        Ok(None)
    }

    /// Execute element-wise binary operation on Metal GPU
    fn execute_elementwise_binary(&self, pattern: &ElementWiseBinaryPattern) -> Result<()> {
        // Get kernel name
        let kernel_name = pattern.op_type.kernel_name(pattern.ty).ok_or_else(|| {
            BackendError::UnsupportedOperation(format!(
                "Operation {:?} not supported for type {:?}",
                pattern.op_type, pattern.ty
            ))
        })?;

        // Get pipeline from cache
        let pipeline = {
            let mut cache = self.pipeline_cache.write();
            cache.get_pipeline(&kernel_name)?.clone()
        };

        // Get Metal buffers from memory manager
        let memory = self.memory.read();
        let buffer_a = memory.get_buffer(crate::backend::BufferHandle::new(pattern.buffer_a))?;
        let buffer_b = memory.get_buffer(crate::backend::BufferHandle::new(pattern.buffer_b))?;
        let buffer_c = memory.get_buffer(crate::backend::BufferHandle::new(pattern.buffer_c))?;
        drop(memory); // Release lock before GPU execution

        // Create command buffer and compute encoder
        let command_buffer = self.command_queue.new_command_buffer();
        let compute_encoder = command_buffer.new_compute_command_encoder();

        // Set compute pipeline state
        compute_encoder.set_compute_pipeline_state(&pipeline);

        // Set buffer arguments
        // Buffer 0: input A
        // Buffer 1: input B
        // Buffer 2: output C
        // Buffer 3: element count (as constant)
        compute_encoder.set_buffer(0, Some(buffer_a), 0);
        compute_encoder.set_buffer(1, Some(buffer_b), 0);
        compute_encoder.set_buffer(2, Some(buffer_c), 0);
        compute_encoder.set_bytes(
            3,
            std::mem::size_of::<u32>() as u64,
            &(pattern.n as u32) as *const u32 as *const _,
        );

        // Calculate thread group sizes
        // Apple Silicon GPUs work best with 256 threads per group
        let thread_group_size = 256;
        let thread_groups = (pattern.n + thread_group_size - 1) / thread_group_size;

        // Dispatch compute kernel
        compute_encoder.dispatch_thread_groups(
            MTLSize::new(thread_groups as u64, 1, 1),
            MTLSize::new(thread_group_size as u64, 1, 1),
        );

        compute_encoder.end_encoding();

        // Submit command buffer and wait for completion
        command_buffer.commit();
        command_buffer.wait_until_completed();

        Ok(())
    }

    /// Execute element-wise unary operation on Metal GPU
    fn execute_elementwise_unary(&self, pattern: &ElementWiseBinaryPattern) -> Result<()> {
        // Get kernel name
        let kernel_name = pattern.op_type.kernel_name(pattern.ty).ok_or_else(|| {
            BackendError::UnsupportedOperation(format!(
                "Operation {:?} not supported for type {:?}",
                pattern.op_type, pattern.ty
            ))
        })?;

        // Get pipeline from cache
        let pipeline = {
            let mut cache = self.pipeline_cache.write();
            cache.get_pipeline(&kernel_name)?.clone()
        };

        // Get Metal buffers from memory manager
        // Note: pattern.buffer_b is unused for unary operations
        let memory = self.memory.read();
        let buffer_a = memory.get_buffer(crate::backend::BufferHandle::new(pattern.buffer_a))?;
        let buffer_c = memory.get_buffer(crate::backend::BufferHandle::new(pattern.buffer_c))?;
        drop(memory); // Release lock before GPU execution

        // Create command buffer and compute encoder
        let command_buffer = self.command_queue.new_command_buffer();
        let compute_encoder = command_buffer.new_compute_command_encoder();

        // Set compute pipeline state
        compute_encoder.set_compute_pipeline_state(&pipeline);

        // Set buffer arguments for unary operation
        // Buffer 0: input A
        // Buffer 1: output C
        // Buffer 2: element count (as constant)
        compute_encoder.set_buffer(0, Some(buffer_a), 0);
        compute_encoder.set_buffer(1, Some(buffer_c), 0);
        compute_encoder.set_bytes(
            2,
            std::mem::size_of::<u32>() as u64,
            &(pattern.n as u32) as *const u32 as *const _,
        );

        // Calculate thread group sizes
        // Apple Silicon GPUs work best with 256 threads per group
        let thread_group_size = 256;
        let thread_groups = (pattern.n + thread_group_size - 1) / thread_group_size;

        // Dispatch compute kernel
        compute_encoder.dispatch_thread_groups(
            MTLSize::new(thread_groups as u64, 1, 1),
            MTLSize::new(thread_group_size as u64, 1, 1),
        );

        compute_encoder.end_encoding();

        // Submit command buffer and wait for completion
        command_buffer.commit();
        command_buffer.wait_until_completed();

        Ok(())
    }
}
