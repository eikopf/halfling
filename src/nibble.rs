//! Byte-width nibbles representing arbitrary data.
//!
//! # Representation in Memory
//! Calling these structures "nibbles" is something of a lie: fundamentally, Rust expects data to
//! be byte-aligned. As a result, a [`Nibble`] is effectively a nice API around a `u8`,
//! guaranteeing[^1] that its upper four bits (the upper nibble) will be uniformly zero.
//!
//! This is admittedly irritating, but it does have a few nice benefits; namely
//! - common operations on [`Nibble`]s correspond directly to operations on `u8`s, which typically
//! map to single instructions at the machine code level;
//! - the invalid bit patterns can be marked as such, and this enables the
//! [null value optimization](std::option#representation).
//!
//! You should see *no* overhead for using a [`Nibble`] (over a similarly checked `u8`), and any
//! such behaviour is considered to be a bug. They are intended to be [zero cost
//! abstractions](https://boats.gitlab.io/blog/post/zero-cost-abstractions/), and so they are
//! implemented in such a way that they effectively "vanish" at compile-time.[^2]
//!
//! # Traits and Intended Usage
//! A new user of `halfling` will probably notice that [`Nibble`] doesn't implement common numeric
//! traits like [`std::ops::Add`], [`std::ops::Mul`], or [`std::ops::Sub`]. This is entirely
//! deliberate, and will not change: *[`Nibble`]s are not intended to directly represent
//! integers*.
//!
//! The entire point of this type is to represent arbitrary data in 4 bits, and adding traits and
//! methods that imply it is an unsigned integer would detract from this purpose. If you want
//! specific integer behaviour, consider using [`I4`](crate::integer::I4) or
//! [`U4`](crate::integer::U4) instead.
//!
//! [`Nibble`]s do support bitwise operations, however, as the bit pattern is considered to be
//! "unopinionated data" with no particular interpretation. This usage typically appears when
//! using [`Nibble`]s as small bitsets, or in dense collections of small enumerations.[^3]
//!
//! [^1]: Of course, this assumes that the [`Nibble`] in question was created correctly; invalid
//! calls to `Nibble::new_unchecked` violate these guarantees and are undefined behaviour, as
//! they correspond to invalid calls to [`std::mem::transmute`].
//!
//! [^2]: Again, it's more appropriate to say that they *ought* to vanish at compile time. Edge
//! cases in `rustc` and LLVM can produce bizarre inefficiencies, and we welcome bug reports and
//! issues that document/reproduce this behaviour.
//!
//! [^3]: See [`konig`](https://crates.io/crates/konig)'s `QuadBoard` for an example of this
//! second kind of usage, where the dense collection is given by 4 `u64` channels, and where each
//! horizontal section of 4 bits corresponds to a particular chess piece at some location.

use crate::{
    error::InvalidNibbleError,
    internal::{SignedNibbleValue, UnsignedNibbleValue},
};

/// A trait for types which act like nibbles, in the sense
/// that they have exactly 16 possible variants and can be
/// converted into and from [`Nibble`]s.
pub trait NibbleValue: Into<Nibble> + From<Nibble> {
    /// The "underlying value," in the sense that the implementing
    /// type represents a subset of this value and is (probably)
    /// backed by it.
    type Inner: TryInto<Self> + From<Self>;

    /// Returns a `Self::Inner` corresponding to the value of `self`. Generally,
    /// prefer using other functions that operate on values of `Self` instead,
    /// since they can provide additional API guarantees.
    ///
    /// Types like [`U4`](crate::integer::U4), [`I4`](crate::integer::I4), and
    /// [`Nibble`] provide this functionality in terms of corresponding `get(&self)`
    /// functions, which are `const` and so cannot be included in this trait; implementing
    /// types are encouraged to do the same.
    fn inner(&self) -> Self::Inner;
}

/// A byte-width nibble, representing a 4-bit unit of data.
///
/// While this type does not explicitly guarantee any
/// particular memory layout, it does guarantee that the
/// [null pointer optimization](std::option#representation)
/// applies: [`Option<Nibble>`](std::option) will always have the same size
/// and alignment as `Nibble`.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct Nibble(UnsignedNibbleValue);

// LOCAL TRAITS

impl NibbleValue for Nibble {
    type Inner = u8;

    fn inner(&self) -> Self::Inner {
        self.get()
    }
}

// DISPLAY TRAITS

impl std::fmt::Binary for Nibble {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <u8 as std::fmt::Binary>::fmt(&u8::from(*self), f)
    }
}

impl std::fmt::Octal for Nibble {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <u8 as std::fmt::Octal>::fmt(&u8::from(*self), f)
    }
}

impl std::fmt::LowerHex for Nibble {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <u8 as std::fmt::LowerHex>::fmt(&u8::from(*self), f)
    }
}

impl std::fmt::UpperHex for Nibble {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <u8 as std::fmt::UpperHex>::fmt(&u8::from(*self), f)
    }
}

impl std::fmt::Display for Nibble {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // this needs to be 6 (rather than 4) because the width includes
        // the prefix.
        write!(f, "{:#06b}", self)
    }
}

// OPERATOR TRAITS

impl std::ops::BitAnd for Nibble {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        let left: u8 = self.into();
        let right: u8 = rhs.into();

        // upper bits are all zero,
        // so no need to mask them off
        let result: u8 = left & right;
        unsafe { Nibble::new_unchecked(result) }
    }
}

impl std::ops::BitAndAssign for Nibble {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl std::ops::BitOr for Nibble {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        let left: u8 = self.into();
        let right: u8 = rhs.into();

        // the upper 4 bits are all zero,
        // so no need to mask them off.
        let result = left | right;
        unsafe { Nibble::new_unchecked(result) }
    }
}

impl std::ops::BitOrAssign for Nibble {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl std::ops::BitXor for Nibble {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        let left: u8 = self.into();
        let right: u8 = rhs.into();
        let result = left ^ right;
        unsafe { Nibble::new_unchecked(result) }
    }
}

impl std::ops::BitXorAssign for Nibble {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}

impl std::ops::Not for Nibble {
    type Output = Self;

    fn not(self) -> Self::Output {
        let value: u8 = self.into();
        let mask: u8 = 0b00001111;

        // a bitwise not will flip the upper four bits
        // to ones, so we mask them off.
        let result: u8 = !value & mask;
        unsafe { Nibble::new_unchecked(result) }
    }
}

impl std::ops::Shl<u8> for Nibble {
    type Output = Nibble;

    fn shl(self, rhs: u8) -> Self::Output {
        let lhs: u8 = self.into();
        let result = lhs << rhs;

        match Nibble::try_from(result) {
            Ok(nibble) => nibble,
            Err(_) => panic!(
                "The value {:#x} created by {} << {} cannot be represented as a nibble.",
                result, lhs, rhs
            ),
        }
    }
}

impl std::ops::ShlAssign<u8> for Nibble {
    fn shl_assign(&mut self, rhs: u8) {
        *self = *self << rhs;
    }
}

impl std::ops::Shr<u8> for Nibble {
    type Output = Nibble;

    fn shr(self, rhs: u8) -> Self::Output {
        let lhs: u8 = self.into();
        let result = lhs >> rhs;

        match Nibble::try_from(result) {
            Ok(nibble) => nibble,
            Err(_) => panic!(
                "The value {:#x} created by {} >> {} cannot be represented as a nibble.",
                result, lhs, rhs
            ),
        }
    }
}

impl std::ops::ShrAssign<u8> for Nibble {
    fn shr_assign(&mut self, rhs: u8) {
        *self = *self >> rhs;
    }
}

// CONVERSION TRAITS

impl From<UnsignedNibbleValue> for Nibble {
    fn from(value: UnsignedNibbleValue) -> Self {
        Self(value)
    }
}

impl From<Nibble> for UnsignedNibbleValue {
    fn from(value: Nibble) -> Self {
        value.0
    }
}

impl From<Nibble> for u8 {
    fn from(value: Nibble) -> Self {
        value.unsigned_value() as u8
    }
}

impl TryFrom<u8> for Nibble {
    type Error = InvalidNibbleError<u8>;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0..=15 => Ok(unsafe { Nibble::new_unchecked(value) }),
            _ => Err(InvalidNibbleError::Unrepresentable(value)),
        }
    }
}

impl Nibble {
    /// The minimum number of bits required to represent a nibble.
    ///
    /// As opposed to the primitive integer types, this value is not
    /// the same as `std::mem::sizeof<Nibble>() * 8`; instead it reflects
    /// the smallest possible size that a nibble could be packed into.
    pub const BITS: u32 = 4u32;

    /// Constructs a new [`Nibble`] representing the given value
    /// without checking invariants.
    ///
    /// # Safety
    /// `value` must be strictly less than 16.
    #[inline]
    pub const unsafe fn new_unchecked(value: u8) -> Self {
        std::mem::transmute(value)
    }

    /// Constructs a new [`Nibble`] representing the given value,
    /// or panics if this is not possible. Prefer using `try_from`
    /// instead if you do not need the construction to be `const`.
    ///
    /// # Panics
    /// This functions will panic if `value >= 16`.
    #[inline]
    pub const fn new_checked(value: u8) -> Self {
        assert!(Nibble::can_represent(value));
        unsafe { Nibble::new_unchecked(value) }
    }

    /// Consumes `self` and returns a `u8` representing its value, guaranteed
    /// to be at most 15.
    #[inline]
    pub const fn get(self) -> u8 {
        unsafe { std::mem::transmute(self) }
    }

    /// Converts a byte (`u8`) into a pair of nibbles, where
    /// the upper nibble is on the left and the lower nibble is
    /// on the right.
    pub const fn pair_from_byte(value: u8) -> (Self, Self) {
        let upper = unsafe { Self::new_unchecked(value >> 4) };
        let lower = unsafe { Self::new_unchecked(value & 0x0F) };
        (upper, lower)
    }

    /// Consumes `self` and returns the underlying [`UnsignedNibbleValue`].
    #[inline]
    pub(crate) const fn unsigned_value(self) -> UnsignedNibbleValue {
        self.0
    }

    /// Consumes `self` and returns the corresponding [`SignedNibbleValue`].
    #[inline]
    pub(crate) const fn signed_value(self) -> SignedNibbleValue {
        self.0.signed_value()
    }

    /// Checks whether the given `u8` can be safely converted into a [`Nibble`],
    /// returning this information as a `bool`.
    ///
    /// Prefer using this check over an ad-hoc implementation before making calls
    /// to `Nibble::new_unchecked`, since it is faster than the naive `x < 16` and
    /// can be tested in isolation.
    #[inline]
    pub(crate) const fn can_represent(value: u8) -> bool {
        (value & 0xF0) == 0x00
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn size_of_option_nibble_equals_size_of_nibble() {
        assert_eq!(
            std::mem::size_of::<Option<Nibble>>(),
            std::mem::size_of::<Nibble>()
        )
    }

    #[test]
    fn representable_nibble_values_transmute_correctly() {
        for i in 0..=15u8 {
            let nibble: Nibble = unsafe { Nibble::new_unchecked(i) };
            assert_eq!(nibble.get(), i);
        }
    }

    #[test]
    fn nibble_try_from_u8_is_correct() {
        // acceptable nibble values
        for value in 0..=15 {
            assert!(Nibble::try_from(value as u8).is_ok());
        }

        // unacceptable nibble values
        for value in 16..=u8::MAX {
            assert!(Nibble::try_from(value).is_err());
        }
    }

    #[test]
    fn nibble_into_u8_is_correct() {
        for i in 0..=15 {
            let nibble = Nibble::try_from(i as u8).unwrap();
            let byte: u8 = nibble.into();
            assert_eq!(byte, i);
        }
    }

    #[test]
    fn unsafe_nibble_new_unchecked_is_valid_given_invariants() {
        for i in 0..=15 {
            let nibble = unsafe { Nibble::new_unchecked(i) };
            let byte: u8 = nibble.into();
            assert_eq!(byte, i);
        }
    }

    #[test]
    fn bitwise_not_produces_valid_nibbles() {
        for value in 0u8..15u8 {
            let nibble = Nibble::try_from(value).unwrap();
            let complement = !nibble;
            eprintln!("{:#06b} --> {:#06b}", nibble, complement);
            assert!(nibble.get() + complement.get() == 15u8);
        }
    }

    #[test]
    fn shl_produces_correct_values() {
        let one = Nibble::try_from(1u8).unwrap();
        let two = one << 1;
        let four = one << 2;
        let eight = one << 3;

        assert_eq!(one.get(), 0b0001);
        assert_eq!(two.get(), 0b0010);
        assert_eq!(four.get(), 0b0100);
        assert_eq!(eight.get(), 0b1000);
    }

    #[test]
    fn shr_produces_correct_values() {
        let fifteen = Nibble::try_from(15u8).unwrap();
        let seven = fifteen >> 1;
        let three = fifteen >> 2;
        let one = fifteen >> 3;

        assert_eq!(fifteen.get(), 0b1111);
        assert_eq!(seven.get(), 0b0111);
        assert_eq!(three.get(), 0b0011);
        assert_eq!(one.get(), 0b0001);
    }

    #[test]
    fn nibble_can_represent_u8_check_is_correct() {
        // valid cases
        for i in 0..=15u8 {
            assert!(Nibble::can_represent(i));
        }

        // invalid cases
        for i in 16..=u8::MAX {
            assert!(!Nibble::can_represent(i));
        }
    }
}
