//! Basic utilities and structures for handling nibbles, both in raw data and integral forms.
//!
//! # Nibbles
//! A [nibble](https://en.wikipedia.org/wiki/Nibble) (sometimes also *nybble* or *nybl*)
//! is a 4-bit unit of data, equivalent in size to a single-digit hexadecimal number.
//! Historically, nibbles were used in early computers to represent small enumerations, e.g.
//! the individual digits of a base-10 number, but today they are largely API details (as
//! opposed to genuinely necessary memory-saving constructs).
//!
//! `halfling`'s [`Nibble`] is a byte-width struct containing a single nibble, which enables
//! the [niche value optimization](https://www.noahlev.org/papers/popl22src-filling-a-niche.pdf)
//! (a [`Nibble`] has 4 unused bits, and hence 240 such niches are available).
//! They are byte-width due to [Rust's fundamental expectation that all types are at least
//! byte-aligned](https://doc.rust-lang.org/reference/type-layout.html), which prevents us
//! from constructing a single type that genuinely consumes only a nibble of memory.

#[warn(missing_docs)]
#[warn(rustdoc::all)]
#[warn(clippy::missing_docs_in_private_items)]
#[warn(clippy::style)]
#[warn(clippy::todo)]
#[warn(clippy::missing_errors_doc)]
#[warn(clippy::missing_panics_doc)]
#[warn(clippy::missing_safety_doc)]
mod internal;
use thiserror::Error;

/// The error produced when trying to convert
/// an unrepresentable integer into a [`Nibble`].
#[derive(Debug, Error)]
pub enum InvalidNibbleError<Src: std::fmt::LowerHex> {
    /// Occurs when attempting to construct a [`Nibble`] with
    /// a value larger than a byte.
    #[error("Attempted to construct a nibble representing a value larger than a byte.")]
    TooLarge(Src),
    /// Occurs when attempting to construct a [`Nibble`] with
    /// an unrepresentable byte, i.e. a byte whose upper 4 bits are not uniformly 0.
    #[error("Attempted to construct a nibble representing {0:#06x}.")]
    Unrepresentable(Src),
}

/// A byte-width nibble, representing a 4-bit unit of data.
///
/// While this type does not explicitly guarantee any
/// particular memory layout, it does guarantee that the
/// [null pointer optimization](std::option#representation)
/// applies: [`Option<Nibble>`](std::option) will always have the same size
/// and alignment as `Nibble`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(transparent)]
pub struct Nibble(internal::UnsignedNibbleValue);

// CONVERSION TRAITS

impl From<internal::UnsignedNibbleValue> for Nibble {
    fn from(value: internal::UnsignedNibbleValue) -> Self {
        Self(value)
    }
}

impl From<Nibble> for internal::UnsignedNibbleValue {
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

// OTHER IMPLS

impl Nibble {
    /// The minimum number of bits required to represent a nibble.
    ///
    /// As opposed to the primitive integer types, this value is not
    /// the same as `std::mem::sizeof<Nibble>() * 8`; instead it reflects
    /// the smallest possible size that a nibble could be packed into.
    pub const BITS: u32 = 4u32;

    /// Returns a representation of `self` as a `Bits` value.
    pub fn as_bits(&self) -> Bits {
        (*self).into()
    }

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
    pub const fn get(&self) -> u8 {
        self.0 as u8
    }

    /// Converts a byte (`u8`) into a pair of nibbles, where
    /// the upper nibble is on the left and the lower nibble is
    /// on the right.
    #[inline]
    pub const fn pair_from_byte(value: u8) -> (Self, Self) {
        let upper = unsafe { Self::new_unchecked(value >> 4) };
        let lower = unsafe { Self::new_unchecked(value & 0x0F) };
        (upper, lower)
    }

    /// Consumes `self` and returns the underlying [`UnsignedNibbleValue`].
    #[inline]
    pub(crate) const fn unsigned_value(self) -> internal::UnsignedNibbleValue {
        self.0
    }

    /// Checks whether the given `u8` can be safely converted into a [`Nibble`],
    /// returning this information as a `bool`.
    ///
    /// Prefer using this check over an ad-hoc implementation before making calls
    /// to `Nibble::new_unchecked`, since it is faster than the naive `x < 16` and
    /// can be tested independently.
    #[inline]
    pub(crate) const fn can_represent(value: u8) -> bool {
        (value & 0xF0) == 0x00
    }
}

/// The bits of a [`Nibble`].
///
/// Conceptually, the bits in a [`Bits`] are
/// stored in *reverse* order, so calling
/// `Bits::first_bit_is_set()` will return the
/// least significant bit.
#[derive(Debug, Default, PartialEq, Eq, Clone, Copy)]
pub struct Bits(bool, bool, bool, bool);

impl From<Nibble> for Bits {
    fn from(value: Nibble) -> Self {
        let value: u8 = value.get();

        Self(
            (value & 0b0001) == 1,
            (value & 0b0010) == 2,
            (value & 0b0100) == 4,
            (value & 0b1000) == 8,
        )
    }
}

impl From<Bits> for Nibble {
    fn from(value: Bits) -> Self {
        let bit1: u8 = value.0.into();
        let bit2: u8 = value.1.into();
        let bit3: u8 = value.2.into();
        let bit4: u8 = value.3.into();

        unsafe { Nibble::new_unchecked(bit1 + (bit2 << 1) + (bit3 << 2) + (bit4 << 3)) }
    }
}

impl<T> From<Bits> for (T, T, T, T)
where
    T: From<bool>,
{
    fn from(value: Bits) -> Self {
        value.into()
    }
}

impl Bits {
    /// A [`Bits`] with all bits set to 0.
    pub const CLEARED: Self = Self(false, false, false, false);

    /// Returns the least significant bit.
    pub const fn first_bit_is_set(&self) -> bool {
        self.0
    }

    /// Returns the second least signficant bit.
    pub const fn second_bit_is_set(&self) -> bool {
        self.1
    }

    /// Returns the second most significant bit.
    pub const fn third_bit_is_set(&self) -> bool {
        self.2
    }

    /// Returns the most signficant bit.
    pub const fn fourth_bit_is_set(&self) -> bool {
        self.3
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
