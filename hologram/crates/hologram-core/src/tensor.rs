//! Multi-dimensional tensor abstraction
//!
//! Provides PyTorch-compatible tensor semantics over Sigmatics buffers.
//! Tensors are views with shape, strides, and offset into underlying memory.

use crate::buffer::Buffer;
use crate::error::{Error, Result};
use std::marker::PhantomData;

/// Multi-dimensional tensor with shape and stride information
///
/// A `Tensor<T>` is a view into a `Buffer<T>` with:
/// - **Shape**: Dimensions of the tensor (e.g., [batch, channels, height, width])
/// - **Strides**: Step sizes for each dimension in elements
/// - **Offset**: Starting element in the buffer
///
/// # Memory Layout
///
/// Tensors use **row-major (C-contiguous)** layout by default, compatible with PyTorch.
/// Strides determine how to navigate the flat buffer to access multi-dim indices.
///
/// For a 2D tensor [rows, cols], element at [i, j] is at:
/// `offset + i * stride[0] + j * stride[1]`
///
/// # Examples
///
/// ```text
/// use hologram_stdlib::{Executor, Tensor};
///
/// let exec = Executor::new()?;
/// let buffer = exec.allocate::<f32>(24)?;
///
/// // Create 2D tensor: 4x6 matrix
/// let tensor = Tensor::from_buffer(buffer, vec![4, 6])?;
/// assert_eq!(tensor.shape(), &[4, 6]);
/// assert_eq!(tensor.strides(), &[6, 1]); // row-major
///
/// // Create with explicit strides (column-major)
/// let col_major = Tensor::from_buffer_with_strides(
///     buffer,
///     vec![4, 6],
///     vec![1, 4],  // column-major strides
/// )?;
/// ```
pub struct Tensor<T> {
    /// Underlying buffer
    buffer: Buffer<T>,
    /// Tensor shape (dimensions)
    shape: Vec<usize>,
    /// Strides in elements (not bytes)
    strides: Vec<usize>,
    /// Offset in elements from buffer start
    offset: usize,
    _marker: PhantomData<T>,
}

impl<T: bytemuck::Pod> Tensor<T> {
    /// Create a tensor from a buffer with the given shape
    ///
    /// Uses row-major (C-contiguous) layout by default.
    /// Buffer must be linear and large enough for the shape.
    pub fn from_buffer(buffer: Buffer<T>, shape: Vec<usize>) -> Result<Self> {
        if !buffer.is_linear() {
            return Err(Error::InvalidOperation("Tensor requires linear buffer".to_string()));
        }

        // Compute total elements
        let numel: usize = shape.iter().product();
        if buffer.len() < numel {
            return Err(Error::InvalidOperation(format!(
                "Buffer too small: need {} elements, have {}",
                numel,
                buffer.len()
            )));
        }

        // Compute row-major strides
        let strides = Self::compute_row_major_strides(&shape);

        Ok(Self {
            buffer,
            shape,
            strides,
            offset: 0,
            _marker: PhantomData,
        })
    }

    /// Create a tensor with explicit strides
    pub fn from_buffer_with_strides(buffer: Buffer<T>, shape: Vec<usize>, strides: Vec<usize>) -> Result<Self> {
        if !buffer.is_linear() {
            return Err(Error::InvalidOperation("Tensor requires linear buffer".to_string()));
        }

        if shape.len() != strides.len() {
            return Err(Error::InvalidOperation(format!(
                "Shape and strides must have same length: {} vs {}",
                shape.len(),
                strides.len()
            )));
        }

        // Compute required buffer size
        let max_offset = Self::compute_max_offset(&shape, &strides);
        if buffer.len() < max_offset {
            return Err(Error::InvalidOperation(format!(
                "Buffer too small: need at least {} elements, have {}",
                max_offset,
                buffer.len()
            )));
        }

        Ok(Self {
            buffer,
            shape,
            strides,
            offset: 0,
            _marker: PhantomData,
        })
    }

    /// Get tensor shape
    pub fn shape(&self) -> &[usize] {
        &self.shape
    }

    /// Get tensor strides
    pub fn strides(&self) -> &[usize] {
        &self.strides
    }

    /// Get tensor offset
    pub fn offset(&self) -> usize {
        self.offset
    }

    /// Get number of dimensions
    pub fn ndim(&self) -> usize {
        self.shape.len()
    }

    /// Get total number of elements
    pub fn numel(&self) -> usize {
        self.shape.iter().product()
    }

    /// Get underlying buffer reference
    pub fn buffer(&self) -> &Buffer<T> {
        &self.buffer
    }

    /// Get mutable buffer reference
    pub fn buffer_mut(&mut self) -> &mut Buffer<T> {
        &mut self.buffer
    }

    /// Check if tensor is contiguous (row-major)
    pub fn is_contiguous(&self) -> bool {
        let expected_strides = Self::compute_row_major_strides(&self.shape);
        self.strides == expected_strides
    }

    /// Create a contiguous copy of this tensor
    ///
    /// If the tensor is already contiguous, returns a clone.
    /// If not, creates a new buffer with row-major layout and copies
    /// all elements from the non-contiguous tensor.
    ///
    /// # Example
    ///
    /// ```text
    /// // Create a non-contiguous tensor via transpose
    /// let t = Tensor::from_buffer(buf, vec![4, 6])?;
    /// let t_transposed = t.transpose()?; // Non-contiguous
    /// assert!(!t_transposed.is_contiguous());
    ///
    /// // Make it contiguous
    /// let t_cont = t_transposed.contiguous(&mut exec)?;
    /// assert!(t_cont.is_contiguous());
    /// ```
    pub fn contiguous(&self, exec: &mut crate::executor::Executor) -> Result<Self>
    where
        T: Copy + std::fmt::Debug,
    {
        // If already contiguous, just clone
        if self.is_contiguous() {
            return Ok(self.clone());
        }

        // Allocate new buffer with row-major layout
        let numel = self.numel();
        let mut new_buffer = exec.allocate::<T>(numel)?;

        // Get full source buffer data
        let full_src_data = self.buffer.to_vec(exec)?;

        // Extract data in contiguous order according to strides
        let mut contiguous_data = Vec::with_capacity(numel);

        // Iterate through all multi-dimensional indices
        self.iterate_indices(|indices| {
            // Compute flat offset in source buffer using strides
            let src_offset = self.offset + indices.iter().zip(&self.strides).map(|(i, s)| i * s).sum::<usize>();
            contiguous_data.push(full_src_data[src_offset]);
        });

        // Write contiguous data to new buffer
        new_buffer.copy_from_slice(exec, &contiguous_data)?;

        // Create new contiguous tensor
        Self::from_buffer(new_buffer, self.shape.clone())
    }

    /// Helper: iterate through all multi-dimensional indices
    fn iterate_indices<F>(&self, mut f: F)
    where
        F: FnMut(&[usize]),
    {
        let mut indices = vec![0; self.shape.len()];
        let numel = self.numel();

        for _ in 0..numel {
            f(&indices);

            // Increment indices (rightmost increments fastest, row-major)
            for dim in (0..self.shape.len()).rev() {
                indices[dim] += 1;
                if indices[dim] < self.shape[dim] {
                    break;
                }
                indices[dim] = 0;
            }
        }
    }

    /// Reshape tensor (must have same number of elements)
    ///
    /// For contiguous tensors, this is a zero-copy view operation.
    /// For non-contiguous tensors, creates a contiguous copy first.
    ///
    /// # Arguments
    ///
    /// * `exec` - Executor (only used if tensor is non-contiguous)
    /// * `new_shape` - New shape (must have same total elements)
    pub fn reshape(&self, exec: &mut crate::executor::Executor, new_shape: Vec<usize>) -> Result<Self>
    where
        T: Copy + std::fmt::Debug,
    {
        let new_numel: usize = new_shape.iter().product();
        if new_numel != self.numel() {
            return Err(Error::InvalidOperation(format!(
                "Cannot reshape: element count mismatch ({} vs {})",
                self.numel(),
                new_numel
            )));
        }

        // For contiguous tensors, just recompute strides (zero-copy)
        if self.is_contiguous() {
            let new_strides = Self::compute_row_major_strides(&new_shape);
            Ok(Self {
                buffer: self.buffer.clone(),
                shape: new_shape,
                strides: new_strides,
                offset: self.offset,
                _marker: PhantomData,
            })
        } else {
            // Non-contiguous tensors: make contiguous first, then reshape
            let contiguous = self.contiguous(exec)?;
            contiguous.reshape(exec, new_shape)
        }
    }

    /// Transpose 2D tensor (swap dimensions 0 and 1)
    pub fn transpose(&self) -> Result<Self> {
        if self.ndim() != 2 {
            return Err(Error::InvalidOperation(format!(
                "transpose() requires 2D tensor, got {}D",
                self.ndim()
            )));
        }

        let mut new_shape = self.shape.clone();
        let mut new_strides = self.strides.clone();

        new_shape.swap(0, 1);
        new_strides.swap(0, 1);

        Ok(Self {
            buffer: self.buffer.clone(),
            shape: new_shape,
            strides: new_strides,
            offset: self.offset,
            _marker: PhantomData,
        })
    }

    /// Permute dimensions
    pub fn permute(&self, dims: Vec<usize>) -> Result<Self> {
        if dims.len() != self.ndim() {
            return Err(Error::InvalidOperation(format!(
                "permute dimensions mismatch: expected {}, got {}",
                self.ndim(),
                dims.len()
            )));
        }

        // Validate all dimensions are unique and in range
        let mut seen = vec![false; self.ndim()];
        for &d in &dims {
            if d >= self.ndim() {
                return Err(Error::InvalidOperation(format!(
                    "permute dimension {} out of range [0, {})",
                    d,
                    self.ndim()
                )));
            }
            if seen[d] {
                return Err(Error::InvalidOperation(format!(
                    "permute dimension {} appears multiple times",
                    d
                )));
            }
            seen[d] = true;
        }

        let mut new_shape = Vec::with_capacity(self.ndim());
        let mut new_strides = Vec::with_capacity(self.ndim());

        for &d in &dims {
            new_shape.push(self.shape[d]);
            new_strides.push(self.strides[d]);
        }

        Ok(Self {
            buffer: self.buffer.clone(),
            shape: new_shape,
            strides: new_strides,
            offset: self.offset,
            _marker: PhantomData,
        })
    }

    /// View as 1D tensor (flattened)
    pub fn view_1d(&self) -> Result<Self> {
        if !self.is_contiguous() {
            return Err(Error::InvalidOperation(
                "view_1d requires contiguous tensor".to_string(),
            ));
        }

        Ok(Self {
            buffer: self.buffer.clone(),
            shape: vec![self.numel()],
            strides: vec![1],
            offset: self.offset,
            _marker: PhantomData,
        })
    }

    /// Select a single index along a dimension (reduces dimensionality by 1)
    ///
    /// # Example
    ///
    /// ```text
    /// let tensor = Tensor::from_buffer(buffer, vec![3, 4, 5])?; // 3x4x5
    /// let selected = tensor.select(0, 1)?; // Select index 1 along dim 0 -> 4x5
    /// assert_eq!(selected.shape(), &[4, 5]);
    /// ```
    pub fn select(&self, dim: usize, index: usize) -> Result<Self> {
        if dim >= self.ndim() {
            return Err(Error::InvalidOperation(format!(
                "select dimension {} out of range for {}D tensor",
                dim,
                self.ndim()
            )));
        }

        if index >= self.shape[dim] {
            return Err(Error::InvalidOperation(format!(
                "select index {} out of range for dimension {} with size {}",
                index, dim, self.shape[dim]
            )));
        }

        // New shape: remove the selected dimension
        let mut new_shape = Vec::with_capacity(self.ndim() - 1);
        let mut new_strides = Vec::with_capacity(self.ndim() - 1);

        for i in 0..self.ndim() {
            if i != dim {
                new_shape.push(self.shape[i]);
                new_strides.push(self.strides[i]);
            }
        }

        // Calculate new offset
        let new_offset = self.offset + index * self.strides[dim];

        Ok(Self {
            buffer: self.buffer.clone(),
            shape: new_shape,
            strides: new_strides,
            offset: new_offset,
            _marker: PhantomData,
        })
    }

    /// Narrow a dimension to a range [start, start+length)
    ///
    /// # Example
    ///
    /// ```text
    /// let tensor = Tensor::from_buffer(buffer, vec![10, 20])?; // 10x20
    /// let narrowed = tensor.narrow(0, 2, 5)?; // Rows 2-6 (5 rows) -> 5x20
    /// assert_eq!(narrowed.shape(), &[5, 20]);
    /// ```
    pub fn narrow(&self, dim: usize, start: usize, length: usize) -> Result<Self> {
        if dim >= self.ndim() {
            return Err(Error::InvalidOperation(format!(
                "narrow dimension {} out of range for {}D tensor",
                dim,
                self.ndim()
            )));
        }

        if start + length > self.shape[dim] {
            return Err(Error::InvalidOperation(format!(
                "narrow range [{}:{}] out of bounds for dimension {} with size {}",
                start,
                start + length,
                dim,
                self.shape[dim]
            )));
        }

        // New shape: update the narrowed dimension
        let mut new_shape = self.shape.clone();
        new_shape[dim] = length;

        // Calculate new offset
        let new_offset = self.offset + start * self.strides[dim];

        Ok(Self {
            buffer: self.buffer.clone(),
            shape: new_shape,
            strides: self.strides.clone(),
            offset: new_offset,
            _marker: PhantomData,
        })
    }

    /// Slice a dimension with start, end, and optional step
    ///
    /// # Example
    ///
    /// ```text
    /// let tensor = Tensor::from_buffer(buffer, vec![10, 20])?; // 10x20
    /// let sliced = tensor.slice(0, Some(2), Some(8), Some(2))?; // Rows 2,4,6 -> 3x20
    /// assert_eq!(sliced.shape(), &[3, 20]);
    /// ```
    pub fn slice(&self, dim: usize, start: Option<usize>, end: Option<usize>, step: Option<usize>) -> Result<Self> {
        if dim >= self.ndim() {
            return Err(Error::InvalidOperation(format!(
                "slice dimension {} out of range for {}D tensor",
                dim,
                self.ndim()
            )));
        }

        let dim_size = self.shape[dim];
        let start = start.unwrap_or(0);
        let end = end.unwrap_or(dim_size).min(dim_size);
        let step = step.unwrap_or(1);

        if step == 0 {
            return Err(Error::InvalidOperation("slice step cannot be zero".to_string()));
        }

        if start >= dim_size {
            return Err(Error::InvalidOperation(format!(
                "slice start {} out of range for dimension {} with size {}",
                start, dim, dim_size
            )));
        }

        // Calculate new shape for the sliced dimension
        let new_dim_size = if end > start { (end - start).div_ceil(step) } else { 0 };

        // New shape and strides
        let mut new_shape = self.shape.clone();
        new_shape[dim] = new_dim_size;

        let mut new_strides = self.strides.clone();
        new_strides[dim] = self.strides[dim] * step;

        // Calculate new offset
        let new_offset = self.offset + start * self.strides[dim];

        Ok(Self {
            buffer: self.buffer.clone(),
            shape: new_shape,
            strides: new_strides,
            offset: new_offset,
            _marker: PhantomData,
        })
    }

    /// Matrix multiply (matmul) for 2D tensors: C = A @ B
    ///
    /// # Requirements
    ///
    /// - Both tensors must be 2D
    /// - Both tensors must be contiguous (row-major layout)
    /// - Inner dimensions must match: A is [M, K], B is [K, N]
    ///
    /// # Returns
    ///
    /// A new tensor C with shape [M, N] containing the matrix product.
    ///
    /// # Example
    ///
    /// ```text
    /// use hologram_stdlib::{Executor, Tensor};
    ///
    /// let exec = Executor::new()?;
    ///
    /// // Create 2x3 matrix A
    /// let a_buf = exec.allocate::<f32>(6)?;
    /// let a = Tensor::from_buffer(a_buf, vec![2, 3])?;
    ///
    /// // Create 3x4 matrix B
    /// let b_buf = exec.allocate::<f32>(12)?;
    /// let b = Tensor::from_buffer(b_buf, vec![3, 4])?;
    ///
    /// // Compute C = A @ B (result is 2x4)
    /// let c = a.matmul(&exec, &b)?;
    /// assert_eq!(c.shape(), &[2, 4]);
    /// ```
    pub fn matmul(&self, exec: &mut crate::executor::Executor, other: &Self) -> Result<Self> {
        // Validate 2D tensors
        if self.ndim() != 2 || other.ndim() != 2 {
            return Err(Error::InvalidOperation(format!(
                "matmul requires 2D tensors, got {}D and {}D",
                self.ndim(),
                other.ndim()
            )));
        }

        // Validate contiguous layout
        if !self.is_contiguous() || !other.is_contiguous() {
            return Err(Error::InvalidOperation(
                "matmul requires contiguous tensors".to_string(),
            ));
        }

        // Extract dimensions: A is [M, K], B is [K, N]
        let m = self.shape[0];
        let k = self.shape[1];
        let k2 = other.shape[0];
        let n = other.shape[1];

        // Validate inner dimensions match
        if k != k2 {
            return Err(Error::InvalidOperation(format!(
                "matmul dimension mismatch: A is [{}x{}], B is [{}x{}]",
                m, k, k2, n
            )));
        }

        // Allocate result tensor C with shape [M, N]
        let c_buffer = exec.allocate::<T>(m * n)?;
        let mut c = Self::from_buffer(c_buffer, vec![m, n])?;

        // Call GEMM operation
        crate::ops::linalg::gemm(exec, &self.buffer, &other.buffer, &mut c.buffer, m, k, n)?;

        Ok(c)
    }

    /// Check if two shapes are broadcast-compatible and compute the result shape
    ///
    /// Broadcasting rules (PyTorch/NumPy compatible):
    /// 1. If tensors have different number of dimensions, prepend 1s to the smaller shape
    /// 2. Two dimensions are compatible if they are equal or one of them is 1
    /// 3. Result shape has the maximum size in each dimension
    ///
    /// # Example
    ///
    /// ```text
    /// // Shape [3, 1, 5] broadcasts with [1, 4, 5] to produce [3, 4, 5]
    /// let shape_a = vec![3, 1, 5];
    /// let shape_b = vec![1, 4, 5];
    /// let result = Tensor::<f32>::broadcast_shapes(&shape_a, &shape_b)?;
    /// assert_eq!(result, vec![3, 4, 5]);
    /// ```
    pub fn broadcast_shapes(shape_a: &[usize], shape_b: &[usize]) -> Result<Vec<usize>> {
        let ndim_a = shape_a.len();
        let ndim_b = shape_b.len();
        let max_ndim = ndim_a.max(ndim_b);

        let mut result_shape = Vec::with_capacity(max_ndim);

        // Iterate from the trailing dimensions
        for i in 0..max_ndim {
            let dim_a_idx = ndim_a.checked_sub(i + 1);
            let dim_b_idx = ndim_b.checked_sub(i + 1);

            let dim_a = dim_a_idx.map(|idx| shape_a[idx]).unwrap_or(1);
            let dim_b = dim_b_idx.map(|idx| shape_b[idx]).unwrap_or(1);

            if dim_a == dim_b {
                result_shape.push(dim_a);
            } else if dim_a == 1 {
                result_shape.push(dim_b);
            } else if dim_b == 1 {
                result_shape.push(dim_a);
            } else {
                return Err(Error::InvalidOperation(format!(
                    "Shapes {:?} and {:?} are not broadcast-compatible at dimension {}",
                    shape_a,
                    shape_b,
                    max_ndim - i - 1
                )));
            }
        }

        // Reverse because we built from trailing dimensions
        result_shape.reverse();
        Ok(result_shape)
    }

    /// Check if this tensor is broadcast-compatible with another tensor
    pub fn is_broadcast_compatible_with(&self, other: &Self) -> bool {
        Self::broadcast_shapes(&self.shape, &other.shape).is_ok()
    }

    /// Compute row-major strides for given shape
    fn compute_row_major_strides(shape: &[usize]) -> Vec<usize> {
        let mut strides = vec![1; shape.len()];
        for i in (0..shape.len().saturating_sub(1)).rev() {
            strides[i] = strides[i + 1] * shape[i + 1];
        }
        strides
    }

    /// Compute maximum offset needed for given shape and strides
    fn compute_max_offset(shape: &[usize], strides: &[usize]) -> usize {
        if shape.is_empty() {
            return 0;
        }

        let mut max_offset = 0;
        for i in 0..shape.len() {
            if shape[i] > 0 {
                max_offset += (shape[i] - 1) * strides[i];
            }
        }
        max_offset + 1
    }
}

impl<T: bytemuck::Pod> Clone for Tensor<T> {
    fn clone(&self) -> Self {
        Self {
            buffer: self.buffer.clone(),
            shape: self.shape.clone(),
            strides: self.strides.clone(),
            offset: self.offset,
            _marker: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executor::Executor;

    #[test]
    fn test_tensor_creation_2d() -> Result<()> {
        let mut exec = Executor::new()?;
        let buffer = exec.allocate::<f32>(24)?;
        let tensor = Tensor::from_buffer(buffer, vec![4, 6])?;

        assert_eq!(tensor.shape(), &[4, 6]);
        assert_eq!(tensor.strides(), &[6, 1]); // row-major
        assert_eq!(tensor.ndim(), 2);
        assert_eq!(tensor.numel(), 24);
        assert!(tensor.is_contiguous());
        Ok(())
    }

    #[test]
    fn test_tensor_creation_3d() -> Result<()> {
        let mut exec = Executor::new()?;
        let buffer = exec.allocate::<f32>(60)?;
        let tensor = Tensor::from_buffer(buffer, vec![3, 4, 5])?;

        assert_eq!(tensor.shape(), &[3, 4, 5]);
        assert_eq!(tensor.strides(), &[20, 5, 1]); // row-major
        assert_eq!(tensor.numel(), 60);
        Ok(())
    }

    #[test]
    fn test_tensor_buffer_too_small() -> Result<()> {
        let mut exec = Executor::new()?;
        let buffer = exec.allocate::<f32>(10)?;
        let result = Tensor::from_buffer(buffer, vec![4, 6]);

        assert!(result.is_err());
        Ok(())
    }

    #[test]
    fn test_tensor_transpose() -> Result<()> {
        let mut exec = Executor::new()?;
        let buffer = exec.allocate::<f32>(12)?;
        let tensor = Tensor::from_buffer(buffer, vec![3, 4])?;

        let transposed = tensor.transpose()?;
        assert_eq!(transposed.shape(), &[4, 3]);
        assert_eq!(transposed.strides(), &[1, 4]); // column-major after transpose
        Ok(())
    }

    #[test]
    fn test_tensor_reshape() -> Result<()> {
        let mut exec = Executor::new()?;
        let buffer = exec.allocate::<f32>(24)?;
        let tensor = Tensor::from_buffer(buffer, vec![4, 6])?;

        let reshaped = tensor.reshape(&mut exec, vec![2, 12])?;
        assert_eq!(reshaped.shape(), &[2, 12]);
        assert_eq!(reshaped.numel(), 24);
        Ok(())
    }

    #[test]
    fn test_tensor_reshape_invalid() -> Result<()> {
        let mut exec = Executor::new()?;
        let buffer = exec.allocate::<f32>(24)?;
        let tensor = Tensor::from_buffer(buffer, vec![4, 6])?;

        let result = tensor.reshape(&mut exec, vec![5, 5]); // 25 != 24
        assert!(result.is_err());
        Ok(())
    }

    #[test]
    fn test_tensor_permute() -> Result<()> {
        let mut exec = Executor::new()?;
        let buffer = exec.allocate::<f32>(24)?;
        let tensor = Tensor::from_buffer(buffer, vec![2, 3, 4])?;

        // Permute to [2, 4, 3]
        let permuted = tensor.permute(vec![0, 2, 1])?;
        assert_eq!(permuted.shape(), &[2, 4, 3]);
        Ok(())
    }

    #[test]
    fn test_tensor_view_1d() -> Result<()> {
        let mut exec = Executor::new()?;
        let buffer = exec.allocate::<f32>(24)?;
        let tensor = Tensor::from_buffer(buffer, vec![4, 6])?;

        let flat = tensor.view_1d()?;
        assert_eq!(flat.shape(), &[24]);
        assert_eq!(flat.strides(), &[1]);
        Ok(())
    }

    #[test]
    fn test_tensor_custom_strides() -> Result<()> {
        let mut exec = Executor::new()?;
        let buffer = exec.allocate::<f32>(24)?;

        // Column-major 4x6 tensor
        let tensor = Tensor::from_buffer_with_strides(
            buffer,
            vec![4, 6],
            vec![1, 4], // column-major
        )?;

        assert_eq!(tensor.shape(), &[4, 6]);
        assert_eq!(tensor.strides(), &[1, 4]);
        assert!(!tensor.is_contiguous()); // Not row-major
        Ok(())
    }

    #[test]
    fn test_tensor_matmul() -> Result<()> {
        let mut exec = Executor::new()?;

        // Create 2x3 matrix A
        let a_buf = exec.allocate::<f32>(6)?;
        let a = Tensor::from_buffer(a_buf, vec![2, 3])?;

        // Create 3x4 matrix B
        let b_buf = exec.allocate::<f32>(12)?;
        let b = Tensor::from_buffer(b_buf, vec![3, 4])?;

        // Compute C = A @ B (result should be 2x4)
        let c = a.matmul(&mut exec, &b)?;

        assert_eq!(c.shape(), &[2, 4]);
        assert_eq!(c.strides(), &[4, 1]); // row-major
        assert!(c.is_contiguous());
        Ok(())
    }

    #[test]
    fn test_tensor_matmul_dimension_mismatch() -> Result<()> {
        let mut exec = Executor::new()?;

        // Create 2x3 matrix A
        let a_buf = exec.allocate::<f32>(6)?;
        let a = Tensor::from_buffer(a_buf, vec![2, 3])?;

        // Create 4x5 matrix B (incompatible: 3 != 4)
        let b_buf = exec.allocate::<f32>(20)?;
        let b = Tensor::from_buffer(b_buf, vec![4, 5])?;

        // Should fail due to dimension mismatch
        let result = a.matmul(&mut exec, &b);
        assert!(result.is_err());
        Ok(())
    }

    #[test]
    fn test_tensor_matmul_requires_2d() -> Result<()> {
        let mut exec = Executor::new()?;

        // Create 1D tensor
        let a_buf = exec.allocate::<f32>(6)?;
        let a = Tensor::from_buffer(a_buf, vec![6])?;

        // Create 2D tensor
        let b_buf = exec.allocate::<f32>(12)?;
        let b = Tensor::from_buffer(b_buf, vec![6, 2])?;

        // Should fail because A is 1D
        let result = a.matmul(&mut exec, &b);
        assert!(result.is_err());
        Ok(())
    }

    #[test]
    fn test_tensor_select() -> Result<()> {
        let mut exec = Executor::new()?;
        let buffer = exec.allocate::<f32>(60)?;
        let tensor = Tensor::from_buffer(buffer, vec![3, 4, 5])?; // 3x4x5

        // Select index 1 along dimension 0 -> 4x5
        let selected = tensor.select(0, 1)?;
        assert_eq!(selected.shape(), &[4, 5]);
        assert_eq!(selected.ndim(), 2);
        assert_eq!(selected.offset, 20); // 1 * (4*5)

        Ok(())
    }

    #[test]
    fn test_tensor_select_invalid_dim() -> Result<()> {
        let mut exec = Executor::new()?;
        let buffer = exec.allocate::<f32>(24)?;
        let tensor = Tensor::from_buffer(buffer, vec![4, 6])?;

        // Try to select on dimension 2 (doesn't exist)
        let result = tensor.select(2, 0);
        assert!(result.is_err());
        Ok(())
    }

    #[test]
    fn test_tensor_select_invalid_index() -> Result<()> {
        let mut exec = Executor::new()?;
        let buffer = exec.allocate::<f32>(24)?;
        let tensor = Tensor::from_buffer(buffer, vec![4, 6])?;

        // Try to select index 4 on dimension 0 (size is 4, so max index is 3)
        let result = tensor.select(0, 4);
        assert!(result.is_err());
        Ok(())
    }

    #[test]
    fn test_tensor_narrow() -> Result<()> {
        let mut exec = Executor::new()?;
        let buffer = exec.allocate::<f32>(200)?;
        let tensor = Tensor::from_buffer(buffer, vec![10, 20])?; // 10x20

        // Narrow dimension 0 to rows 2-6 (5 rows)
        let narrowed = tensor.narrow(0, 2, 5)?;
        assert_eq!(narrowed.shape(), &[5, 20]);
        assert_eq!(narrowed.offset, 40); // 2 * 20
        assert_eq!(narrowed.strides(), &[20, 1]);

        Ok(())
    }

    #[test]
    fn test_tensor_narrow_invalid_range() -> Result<()> {
        let mut exec = Executor::new()?;
        let buffer = exec.allocate::<f32>(200)?;
        let tensor = Tensor::from_buffer(buffer, vec![10, 20])?;

        // Try to narrow beyond dimension size
        let result = tensor.narrow(0, 8, 5); // 8+5=13 > 10
        assert!(result.is_err());
        Ok(())
    }

    #[test]
    fn test_tensor_slice() -> Result<()> {
        let mut exec = Executor::new()?;
        let buffer = exec.allocate::<f32>(200)?;
        let tensor = Tensor::from_buffer(buffer, vec![10, 20])?; // 10x20

        // Slice dimension 0: rows 2,4,6 (start=2, end=8, step=2)
        let sliced = tensor.slice(0, Some(2), Some(8), Some(2))?;
        assert_eq!(sliced.shape(), &[3, 20]); // (8-2)/2 = 3
        assert_eq!(sliced.offset, 40); // 2 * 20
        assert_eq!(sliced.strides(), &[40, 1]); // stride[0] = 20*2

        Ok(())
    }

    #[test]
    fn test_tensor_slice_defaults() -> Result<()> {
        let mut exec = Executor::new()?;
        let buffer = exec.allocate::<f32>(200)?;
        let tensor = Tensor::from_buffer(buffer, vec![10, 20])?;

        // Slice with defaults: all elements with step 1
        let sliced = tensor.slice(0, None, None, None)?;
        assert_eq!(sliced.shape(), &[10, 20]);
        assert_eq!(sliced.offset, 0);
        assert_eq!(sliced.strides(), &[20, 1]);

        Ok(())
    }

    #[test]
    fn test_tensor_slice_step_zero_error() -> Result<()> {
        let mut exec = Executor::new()?;
        let buffer = exec.allocate::<f32>(200)?;
        let tensor = Tensor::from_buffer(buffer, vec![10, 20])?;

        // Step cannot be zero
        let result = tensor.slice(0, None, None, Some(0));
        assert!(result.is_err());
        Ok(())
    }

    #[test]
    fn test_broadcast_shapes_same_shape() -> Result<()> {
        let shape_a = vec![3, 4, 5];
        let shape_b = vec![3, 4, 5];
        let result = Tensor::<f32>::broadcast_shapes(&shape_a, &shape_b)?;
        assert_eq!(result, vec![3, 4, 5]);
        Ok(())
    }

    #[test]
    fn test_broadcast_shapes_with_ones() -> Result<()> {
        let shape_a = vec![3, 1, 5];
        let shape_b = vec![1, 4, 5];
        let result = Tensor::<f32>::broadcast_shapes(&shape_a, &shape_b)?;
        assert_eq!(result, vec![3, 4, 5]);
        Ok(())
    }

    #[test]
    fn test_broadcast_shapes_different_ndim() -> Result<()> {
        // [3, 4, 5] broadcasts with [5] to produce [3, 4, 5]
        let shape_a = vec![3, 4, 5];
        let shape_b = vec![5];
        let result = Tensor::<f32>::broadcast_shapes(&shape_a, &shape_b)?;
        assert_eq!(result, vec![3, 4, 5]);
        Ok(())
    }

    #[test]
    fn test_broadcast_shapes_scalar() -> Result<()> {
        // [3, 4, 5] broadcasts with [] (scalar) to produce [3, 4, 5]
        let shape_a = vec![3, 4, 5];
        let shape_b = vec![];
        let result = Tensor::<f32>::broadcast_shapes(&shape_a, &shape_b)?;
        assert_eq!(result, vec![3, 4, 5]);
        Ok(())
    }

    #[test]
    fn test_broadcast_shapes_incompatible() -> Result<()> {
        // [3, 4] and [5] are incompatible (4 != 5 and neither is 1)
        let shape_a = vec![3, 4];
        let shape_b = vec![5];
        let result = Tensor::<f32>::broadcast_shapes(&shape_a, &shape_b);
        assert!(result.is_err());
        Ok(())
    }

    #[test]
    fn test_is_broadcast_compatible() -> Result<()> {
        let mut exec = Executor::new()?;

        let buf_a = exec.allocate::<f32>(60)?;
        let tensor_a = Tensor::from_buffer(buf_a, vec![3, 4, 5])?;

        let buf_b = exec.allocate::<f32>(5)?;
        let tensor_b = Tensor::from_buffer(buf_b, vec![5])?;

        // [3, 4, 5] is compatible with [5]
        assert!(tensor_a.is_broadcast_compatible_with(&tensor_b));

        Ok(())
    }

    #[test]
    fn test_is_broadcast_incompatible() -> Result<()> {
        let mut exec = Executor::new()?;

        let buf_a = exec.allocate::<f32>(12)?;
        let tensor_a = Tensor::from_buffer(buf_a, vec![3, 4])?;

        let buf_b = exec.allocate::<f32>(5)?;
        let tensor_b = Tensor::from_buffer(buf_b, vec![5])?;

        // [3, 4] is NOT compatible with [5] (4 != 5)
        assert!(!tensor_a.is_broadcast_compatible_with(&tensor_b));

        Ok(())
    }

    #[test]
    fn test_tensor_contiguous_already_contiguous() -> Result<()> {
        let mut exec = Executor::new()?;
        let mut buffer = exec.allocate::<f32>(24)?;

        // Write test data
        let data: Vec<f32> = (0..24).map(|i| i as f32).collect();
        buffer.copy_from_slice(&mut exec, &data)?;

        let tensor = Tensor::from_buffer(buffer, vec![4, 6])?;
        assert!(tensor.is_contiguous());

        // contiguous() on already-contiguous tensor should just clone
        let contiguous = tensor.contiguous(&mut exec)?;
        assert!(contiguous.is_contiguous());
        assert_eq!(contiguous.shape(), tensor.shape());

        Ok(())
    }

    #[test]
    fn test_tensor_contiguous_after_transpose() -> Result<()> {
        let mut exec = Executor::new()?;
        let mut buffer = exec.allocate::<f32>(12)?;

        // Write test data: [[1,2,3,4], [5,6,7,8], [9,10,11,12]]
        let data: Vec<f32> = (1..=12).map(|i| i as f32).collect();
        buffer.copy_from_slice(&mut exec, &data)?;

        let tensor = Tensor::from_buffer(buffer, vec![3, 4])?; // 3x4
        assert!(tensor.is_contiguous());

        // Transpose makes it non-contiguous
        let transposed = tensor.transpose()?; // 4x3
        assert!(!transposed.is_contiguous());
        assert_eq!(transposed.shape(), &[4, 3]);

        // Make it contiguous
        let contiguous = transposed.contiguous(&mut exec)?;
        assert!(contiguous.is_contiguous());
        assert_eq!(contiguous.shape(), &[4, 3]);

        // Verify data is correct (transposed)
        // Original: [[1,2,3,4], [5,6,7,8], [9,10,11,12]]
        // Transposed: [[1,5,9], [2,6,10], [3,7,11], [4,8,12]]
        let result = contiguous.buffer().to_vec(&exec)?;
        assert_eq!(result[0], 1.0); // [0,0]
        assert_eq!(result[1], 5.0); // [0,1]
        assert_eq!(result[2], 9.0); // [0,2]
        assert_eq!(result[3], 2.0); // [1,0]
        assert_eq!(result[6], 3.0); // [2,0]
        assert_eq!(result[11], 12.0); // [3,2]

        Ok(())
    }

    #[test]
    fn test_tensor_reshape_non_contiguous() -> Result<()> {
        let mut exec = Executor::new()?;
        let mut buffer = exec.allocate::<f32>(12)?;

        // Write test data
        let data: Vec<f32> = (1..=12).map(|i| i as f32).collect();
        buffer.copy_from_slice(&mut exec, &data)?;

        let tensor = Tensor::from_buffer(buffer, vec![3, 4])?;

        // Transpose makes it non-contiguous
        let transposed = tensor.transpose()?;
        assert!(!transposed.is_contiguous());

        // Reshape should work by making contiguous first
        let reshaped = transposed.reshape(&mut exec, vec![2, 6])?;
        assert!(reshaped.is_contiguous());
        assert_eq!(reshaped.shape(), &[2, 6]);
        assert_eq!(reshaped.numel(), 12);

        Ok(())
    }
}
