//! Exact rational matrices and vectors for Weyl group elements
//!
//! This module provides matrix and vector representation for Weyl group elements,
//! using exact rational arithmetic to preserve mathematical correctness.

use super::Rational;
use num_traits::{One, Zero};
use std::fmt;
use std::hash::{Hash, Hasher};

/// N-dimensional vector with exact rational coordinates
///
/// Used for simple roots and Weyl group operations in rank-N space.
/// All coordinates are rational numbers for exact arithmetic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RationalVector<const N: usize> {
    /// Vector coordinates
    coords: [Rational; N],
}

impl<const N: usize> RationalVector<N> {
    /// Create vector from array of rationals
    #[must_use]
    pub const fn new(coords: [Rational; N]) -> Self {
        Self { coords }
    }

    /// Create zero vector
    #[must_use]
    pub fn zero() -> Self {
        Self { coords: [Rational::zero(); N] }
    }

    /// Get coordinate at index
    #[must_use]
    pub const fn get(&self, i: usize) -> Rational {
        self.coords[i]
    }

    /// Get all coordinates
    #[must_use]
    pub const fn coords(&self) -> &[Rational; N] {
        &self.coords
    }

    /// Inner product (exact rational arithmetic)
    #[must_use]
    pub fn dot(&self, other: &Self) -> Rational {
        let mut sum = Rational::zero();
        for i in 0..N {
            sum += self.coords[i] * other.coords[i];
        }
        sum
    }

    /// Norm squared: ⟨v, v⟩
    #[must_use]
    pub fn norm_squared(&self) -> Rational {
        self.dot(self)
    }

    /// Vector subtraction
    #[must_use]
    pub fn sub(&self, other: &Self) -> Self {
        let mut result = [Rational::zero(); N];
        for (i, item) in result.iter_mut().enumerate().take(N) {
            *item = self.coords[i] - other.coords[i];
        }
        Self { coords: result }
    }

    /// Scalar multiplication
    #[must_use]
    pub fn scale(&self, scalar: Rational) -> Self {
        let mut result = [Rational::zero(); N];
        for (i, item) in result.iter_mut().enumerate().take(N) {
            *item = self.coords[i] * scalar;
        }
        Self { coords: result }
    }
}

impl<const N: usize> Hash for RationalVector<N> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for coord in &self.coords {
            coord.numer().hash(state);
            coord.denom().hash(state);
        }
    }
}

/// Matrix with exact rational entries
///
/// Used to represent Weyl group elements as matrices. All operations
/// use exact rational arithmetic (no floating point).
///
/// From certified Python implementation: `ExactMatrix` class
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RationalMatrix<const N: usize> {
    /// Matrix data: N×N array of rational numbers
    data: [[Rational; N]; N],
}

impl<const N: usize> RationalMatrix<N> {
    /// Create matrix from 2D array
    #[must_use]
    pub const fn new(data: [[Rational; N]; N]) -> Self {
        Self { data }
    }

    /// Create identity matrix
    ///
    /// # Examples
    ///
    /// ```
    /// use atlas_embeddings::arithmetic::{RationalMatrix, Rational};
    ///
    /// let id = RationalMatrix::<2>::identity();
    /// assert_eq!(id.get(0, 0), Rational::new(1, 1));
    /// assert_eq!(id.get(0, 1), Rational::new(0, 1));
    /// ```
    #[must_use]
    pub fn identity() -> Self {
        let mut data = [[Rational::zero(); N]; N];
        for (i, row) in data.iter_mut().enumerate().take(N) {
            row[i] = Rational::one();
        }
        Self { data }
    }

    /// Create reflection matrix from root vector
    ///
    /// Implements: `R_α = I - 2(α ⊗ α)/⟨α,α⟩`
    ///
    /// This is the matrix representation of the reflection through the
    /// hyperplane perpendicular to α. Uses exact rational arithmetic.
    ///
    /// From certified Python implementation: `simple_reflection()` method
    ///
    /// # Panics
    ///
    /// Panics if root has norm² = 0
    #[must_use]
    pub fn reflection(root: &RationalVector<N>) -> Self {
        let root_norm_sq = root.norm_squared();
        assert!(!root_norm_sq.is_zero(), "Cannot create reflection from zero root");

        let mut data = [[Rational::zero(); N]; N];

        // Compute I - 2(α ⊗ α)/⟨α,α⟩
        for (i, row) in data.iter_mut().enumerate().take(N) {
            #[allow(clippy::needless_range_loop)]
            for j in 0..N {
                // Identity matrix entry
                let delta = if i == j {
                    Rational::one()
                } else {
                    Rational::zero()
                };

                // Outer product entry: α_i * α_j
                let outer_product = root.get(i) * root.get(j);

                // Matrix entry: δ_ij - 2 * α_i * α_j / ⟨α,α⟩
                row[j] = delta - Rational::new(2, 1) * outer_product / root_norm_sq;
            }
        }

        Self { data }
    }

    /// Get entry at (i, j)
    #[must_use]
    pub const fn get(&self, i: usize, j: usize) -> Rational {
        self.data[i][j]
    }

    /// Get reference to entry at (i, j)
    #[must_use]
    pub const fn get_ref(&self, i: usize, j: usize) -> &Rational {
        &self.data[i][j]
    }

    /// Get all data as reference
    #[must_use]
    pub const fn data(&self) -> &[[Rational; N]; N] {
        &self.data
    }

    /// Matrix multiplication (exact rational arithmetic)
    ///
    /// Computes C = A × B where all operations are exact.
    /// This is the composition operation for Weyl group elements.
    #[must_use]
    pub fn multiply(&self, other: &Self) -> Self {
        let mut result = [[Rational::zero(); N]; N];

        for (i, row) in result.iter_mut().enumerate().take(N) {
            #[allow(clippy::needless_range_loop)]
            for j in 0..N {
                let mut sum = Rational::zero();
                for k in 0..N {
                    sum += self.data[i][k] * other.data[k][j];
                }
                row[j] = sum;
            }
        }

        Self { data: result }
    }

    /// Compute trace (sum of diagonal elements)
    #[must_use]
    pub fn trace(&self) -> Rational {
        let mut sum = Rational::zero();
        for i in 0..N {
            sum += self.data[i][i];
        }
        sum
    }

    /// Check if this is the identity matrix
    #[must_use]
    pub fn is_identity(&self) -> bool {
        for i in 0..N {
            for j in 0..N {
                let expected = if i == j {
                    Rational::one()
                } else {
                    Rational::zero()
                };
                if self.data[i][j] != expected {
                    return false;
                }
            }
        }
        true
    }
}

impl<const N: usize> Hash for RationalMatrix<N> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash each entry (numerator and denominator)
        for row in &self.data {
            for entry in row {
                entry.numer().hash(state);
                entry.denom().hash(state);
            }
        }
    }
}

impl<const N: usize> fmt::Display for RationalMatrix<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "[")?;
        for row in &self.data {
            write!(f, "  [")?;
            for (j, entry) in row.iter().enumerate() {
                if j > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}/{}", entry.numer(), entry.denom())?;
            }
            writeln!(f, "]")?;
        }
        write!(f, "]")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_identity_matrix() {
        let id = RationalMatrix::<3>::identity();
        assert!(id.is_identity());
        assert_eq!(id.trace(), Rational::new(3, 1));
    }

    #[test]
    fn test_matrix_multiply_identity() {
        let id = RationalMatrix::<2>::identity();
        let a = RationalMatrix::new([
            [Rational::new(1, 2), Rational::new(3, 4)],
            [Rational::new(5, 6), Rational::new(7, 8)],
        ]);

        let result = a.multiply(&id);
        assert_eq!(result, a);

        let result2 = id.multiply(&a);
        assert_eq!(result2, a);
    }

    #[test]
    fn test_matrix_multiply_exact() {
        // Simple 2x2 multiplication
        let a = RationalMatrix::new([
            [Rational::new(1, 2), Rational::new(1, 3)],
            [Rational::new(1, 4), Rational::new(1, 5)],
        ]);

        let b = RationalMatrix::new([
            [Rational::new(2, 1), Rational::new(0, 1)],
            [Rational::new(0, 1), Rational::new(3, 1)],
        ]);

        let result = a.multiply(&b);

        // Expected: [1/2*2 + 1/3*0,  1/2*0 + 1/3*3] = [1, 1]
        //           [1/4*2 + 1/5*0,  1/4*0 + 1/5*3] = [1/2, 3/5]
        assert_eq!(result.get(0, 0), Rational::new(1, 1));
        assert_eq!(result.get(0, 1), Rational::new(1, 1));
        assert_eq!(result.get(1, 0), Rational::new(1, 2));
        assert_eq!(result.get(1, 1), Rational::new(3, 5));
    }

    #[test]
    fn test_matrix_equality() {
        let a = RationalMatrix::<2>::identity();
        let b = RationalMatrix::<2>::identity();
        assert_eq!(a, b);

        let c = RationalMatrix::new([
            [Rational::new(1, 1), Rational::new(1, 1)],
            [Rational::new(0, 1), Rational::new(1, 1)],
        ]);
        assert_ne!(a, c);
    }

    #[test]
    fn test_matrix_trace() {
        let m = RationalMatrix::new([
            [Rational::new(1, 2), Rational::new(3, 4)],
            [Rational::new(5, 6), Rational::new(7, 8)],
        ]);

        // Trace = 1/2 + 7/8 = 4/8 + 7/8 = 11/8
        assert_eq!(m.trace(), Rational::new(11, 8));
    }
}
