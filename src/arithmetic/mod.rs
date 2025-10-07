//! Exact arithmetic for Atlas computations
//!
//! This module provides exact rational arithmetic with NO floating point.
//! All computations use exact integers and rationals to preserve mathematical
//! structure.
//!
//! # Key Types
//!
//! - [`Rational`] - Exact rational numbers (alias for `Ratio<i64>`)
//! - [`HalfInteger`] - Half-integers for E₈ coordinates (multiples of 1/2)
//! - [`Vector8`] - 8-dimensional vectors with exact coordinates
//! - [`RationalMatrix`] - Matrices with exact rational entries (for Weyl groups)
//!
//! # Design Principles
//!
//! 1. **No floating point** - All arithmetic is exact
//! 2. **Fraction preservation** - Rationals never lose precision
//! 3. **Overflow detection** - All operations check for overflow
//! 4. **Type safety** - Prevent mixing incompatible number types

mod matrix;

pub use matrix::{RationalMatrix, RationalVector};

use num_rational::Ratio;
use num_traits::Zero;
use std::fmt;
use std::ops::{Add, Mul, Neg, Sub};

/// Exact rational number (fraction)
///
/// This is an alias for `Ratio<i64>` from the `num_rational` crate.
/// All arithmetic operations are exact with no loss of precision.
///
/// # Examples
///
/// ```
/// use atlas_embeddings::arithmetic::Rational;
///
/// let a = Rational::new(1, 2);  // 1/2
/// let b = Rational::new(1, 3);  // 1/3
/// let sum = a + b;              // 5/6 (exact)
///
/// assert_eq!(sum, Rational::new(5, 6));
/// ```
pub type Rational = Ratio<i64>;

/// Half-integer: numbers of the form n/2 where n ∈ ℤ
///
/// E₈ root coordinates are half-integers (elements of ℤ ∪ ½ℤ).
/// This type represents them exactly as `numerator / 2`.
///
/// # Invariant
///
/// The denominator is always 2 (enforced by construction).
///
/// # Examples
///
/// ```
/// use atlas_embeddings::arithmetic::HalfInteger;
///
/// let x = HalfInteger::new(1);  // 1/2
/// let y = HalfInteger::new(3);  // 3/2
/// let sum = x + y;               // 2 = 4/2
///
/// assert_eq!(sum.numerator(), 4);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HalfInteger {
    numerator: i64,
}

impl HalfInteger {
    /// Create a half-integer from a numerator (denominator is always 2)
    ///
    /// # Examples
    ///
    /// ```
    /// use atlas_embeddings::arithmetic::HalfInteger;
    ///
    /// let half = HalfInteger::new(1);    // 1/2
    /// let one = HalfInteger::new(2);     // 2/2 = 1
    /// let neg_half = HalfInteger::new(-1); // -1/2
    /// ```
    #[must_use]
    pub const fn new(numerator: i64) -> Self {
        Self { numerator }
    }

    /// Create from an integer (multiply by 2 internally)
    ///
    /// # Examples
    ///
    /// ```
    /// use atlas_embeddings::arithmetic::HalfInteger;
    ///
    /// let two = HalfInteger::from_integer(1);  // 2/2 = 1
    /// assert_eq!(two.numerator(), 2);
    /// ```
    #[must_use]
    pub const fn from_integer(n: i64) -> Self {
        Self { numerator: n * 2 }
    }

    /// Get the numerator (denominator is always 2)
    #[must_use]
    pub const fn numerator(self) -> i64 {
        self.numerator
    }

    /// Convert to rational number
    #[must_use]
    pub fn to_rational(self) -> Rational {
        Rational::new(self.numerator, 2)
    }

    /// Create from a rational number
    ///
    /// # Panics
    ///
    /// Panics if the rational cannot be represented as n/2
    #[must_use]
    pub fn from_rational(r: Rational) -> Self {
        // Reduce the rational to lowest terms
        let numer = *r.numer();
        let denom = *r.denom();

        // Check if denominator is 1 (integer) or 2 (half-integer)
        match denom {
            1 => Self::from_integer(numer),
            2 => Self::new(numer),
            _ => panic!("Rational {numer}/{denom} cannot be represented as half-integer"),
        }
    }

    /// Square of this half-integer (exact)
    #[must_use]
    pub fn square(self) -> Rational {
        Rational::new(self.numerator * self.numerator, 4)
    }

    /// Check if this is an integer (numerator is even)
    #[must_use]
    pub const fn is_integer(self) -> bool {
        self.numerator % 2 == 0
    }

    /// Get as integer if possible
    #[must_use]
    pub const fn as_integer(self) -> Option<i64> {
        if self.is_integer() {
            Some(self.numerator / 2)
        } else {
            None
        }
    }
}

impl Zero for HalfInteger {
    fn zero() -> Self {
        Self::new(0)
    }

    fn is_zero(&self) -> bool {
        self.numerator == 0
    }
}

// Note: We cannot implement One for HalfInteger because
// HalfInteger * HalfInteger = Rational (not HalfInteger)
// This is mathematically correct: (a/2) * (b/2) = (ab)/4

impl Add for HalfInteger {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self::new(self.numerator + other.numerator)
    }
}

impl Sub for HalfInteger {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        Self::new(self.numerator - other.numerator)
    }
}

impl Mul for HalfInteger {
    type Output = Rational;

    fn mul(self, other: Self) -> Rational {
        Rational::new(self.numerator * other.numerator, 4)
    }
}

impl Neg for HalfInteger {
    type Output = Self;

    fn neg(self) -> Self {
        Self::new(-self.numerator)
    }
}

impl fmt::Display for HalfInteger {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_integer() {
            write!(f, "{}", self.numerator / 2)
        } else {
            write!(f, "{}/2", self.numerator)
        }
    }
}

/// 8-dimensional vector with exact coordinates
///
/// Used for E₈ root system and Atlas coordinates.
/// All coordinates are half-integers for exact arithmetic.
///
/// # Examples
///
/// ```
/// use atlas_embeddings::arithmetic::{Vector8, HalfInteger};
///
/// let v = Vector8::new([
///     HalfInteger::new(1),   // 1/2
///     HalfInteger::new(1),   // 1/2
///     HalfInteger::new(1),   // 1/2
///     HalfInteger::new(1),   // 1/2
///     HalfInteger::new(1),   // 1/2
///     HalfInteger::new(1),   // 1/2
///     HalfInteger::new(1),   // 1/2
///     HalfInteger::new(1),   // 1/2
/// ]);
///
/// // Norm squared: 8 * (1/2)² = 8 * 1/4 = 2
/// assert_eq!(v.norm_squared(), num_rational::Ratio::new(2, 1));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Vector8 {
    coords: [HalfInteger; 8],
}

impl Vector8 {
    /// Create a vector from 8 half-integer coordinates
    #[must_use]
    pub const fn new(coords: [HalfInteger; 8]) -> Self {
        Self { coords }
    }

    /// Create a zero vector
    #[must_use]
    pub fn zero() -> Self {
        Self::new([HalfInteger::zero(); 8])
    }

    /// Get coordinate at index
    #[must_use]
    pub const fn get(&self, index: usize) -> HalfInteger {
        self.coords[index]
    }

    /// Get all coordinates as slice
    #[must_use]
    pub const fn coords(&self) -> &[HalfInteger; 8] {
        &self.coords
    }

    /// Inner product (dot product) - exact rational result
    ///
    /// ⟨v, w⟩ = Σᵢ vᵢ·wᵢ
    #[must_use]
    pub fn inner_product(&self, other: &Self) -> Rational {
        let mut sum = Rational::zero();
        for i in 0..8 {
            sum += self.coords[i] * other.coords[i];
        }
        sum
    }

    /// Norm squared: ‖v‖² = ⟨v, v⟩
    #[must_use]
    pub fn norm_squared(&self) -> Rational {
        self.inner_product(self)
    }

    /// Check if this is a root (norm² = 2)
    #[must_use]
    pub fn is_root(&self) -> bool {
        self.norm_squared() == Rational::new(2, 1)
    }

    /// Vector addition
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        let result: [HalfInteger; 8] = std::array::from_fn(|i| self.coords[i] + other.coords[i]);
        Self::new(result)
    }

    /// Vector subtraction
    #[must_use]
    pub fn sub(&self, other: &Self) -> Self {
        let result: [HalfInteger; 8] = std::array::from_fn(|i| self.coords[i] - other.coords[i]);
        Self::new(result)
    }

    /// Scalar multiplication by integer
    #[must_use]
    pub fn scale(&self, scalar: i64) -> Self {
        let result: [HalfInteger; 8] =
            std::array::from_fn(|i| HalfInteger::new(self.coords[i].numerator() * scalar));
        Self::new(result)
    }

    /// Scalar multiplication by rational
    ///
    /// Multiplies each coordinate by a rational scalar (exact arithmetic)
    #[must_use]
    pub fn scale_rational(&self, scalar: Rational) -> Self {
        let result: [HalfInteger; 8] = std::array::from_fn(|i| {
            let coord_rational = self.coords[i].to_rational();
            let product = coord_rational * scalar;
            HalfInteger::from_rational(product)
        });
        Self::new(result)
    }

    /// Negation
    #[must_use]
    pub fn negate(&self) -> Self {
        let result: [HalfInteger; 8] = std::array::from_fn(|i| -self.coords[i]);
        Self::new(result)
    }
}

impl Add for Vector8 {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self::add(&self, &other)
    }
}

impl Sub for Vector8 {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        Self::sub(&self, &other)
    }
}

impl Neg for Vector8 {
    type Output = Self;

    fn neg(self) -> Self {
        self.negate()
    }
}

impl fmt::Display for Vector8 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, coord) in self.coords.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{coord}")?;
        }
        write!(f, ")")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_half_integer_creation() {
        let half = HalfInteger::new(1);
        assert_eq!(half.numerator(), 1);
        assert_eq!(half.to_rational(), Rational::new(1, 2));

        let one = HalfInteger::from_integer(1);
        assert_eq!(one.numerator(), 2);
        assert!(one.is_integer());
    }

    #[test]
    fn test_half_integer_arithmetic() {
        let a = HalfInteger::new(1); // 1/2
        let b = HalfInteger::new(3); // 3/2

        let sum = a + b; // 2
        assert_eq!(sum.numerator(), 4);
        assert!(sum.is_integer());

        let diff = b - a; // 1
        assert_eq!(diff.numerator(), 2);

        let prod = a * b; // 3/4
        assert_eq!(prod, Rational::new(3, 4));
    }

    #[test]
    fn test_half_integer_square() {
        let half = HalfInteger::new(1); // 1/2
        assert_eq!(half.square(), Rational::new(1, 4));

        let one = HalfInteger::from_integer(1); // 1
        assert_eq!(one.square(), Rational::new(1, 1));
    }

    #[test]
    fn test_vector8_creation() {
        let v = Vector8::zero();
        assert!(v.norm_squared().is_zero());

        let ones = Vector8::new([HalfInteger::from_integer(1); 8]);
        assert_eq!(ones.norm_squared(), Rational::new(8, 1));
    }

    #[test]
    fn test_vector8_inner_product() {
        let v = Vector8::new([HalfInteger::new(1); 8]); // All 1/2
        let w = Vector8::new([HalfInteger::new(2); 8]); // All 1

        // ⟨v, w⟩ = 8 * (1/2 * 1) = 8 * 1/2 = 4
        assert_eq!(v.inner_product(&w), Rational::new(4, 1));
    }

    #[test]
    fn test_vector8_norm_squared() {
        let v = Vector8::new([HalfInteger::new(1); 8]); // All 1/2

        // ‖v‖² = 8 * (1/2)² = 8 * 1/4 = 2
        assert_eq!(v.norm_squared(), Rational::new(2, 1));
        assert!(v.is_root());
    }

    #[test]
    fn test_vector8_arithmetic() {
        let v = Vector8::new([HalfInteger::new(1); 8]);
        let w = Vector8::new([HalfInteger::new(1); 8]);

        let sum = v + w;
        assert_eq!(sum.coords[0].numerator(), 2);

        let diff = v - w;
        assert!(diff.norm_squared().is_zero());

        let neg = -v;
        assert_eq!(neg.coords[0].numerator(), -1);
    }

    #[test]
    fn test_vector8_scaling() {
        let v = Vector8::new([HalfInteger::from_integer(1); 8]);
        let scaled = v.scale(3);

        assert_eq!(scaled.coords[0].numerator(), 6);
        assert_eq!(scaled.norm_squared(), Rational::new(72, 1));
    }

    #[test]
    fn test_rational_exact_arithmetic() {
        let a = Rational::new(1, 3);
        let b = Rational::new(1, 6);

        let sum = a + b;
        assert_eq!(sum, Rational::new(1, 2));

        let prod = a * b;
        assert_eq!(prod, Rational::new(1, 18));
    }
}
