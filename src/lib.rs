//! Basic utilities and structures for handling nibbles.
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

#![warn(missing_docs)]
#![warn(rustdoc::all)]
#![warn(clippy::all)]
use thiserror::Error;

#[macro_use]
mod internal;

/// The error produced if a conversion from an integral type to a [`Nibble`] fails.
#[derive(Debug, Error)]
#[error("failed to convert {0:?} into a nibble.")]
pub struct NibbleTryFromIntError<T>(T);

/// A byte-width nibble, representing a 4-bit unit of data.
///
/// # Memory Layout
/// The bit pattern of a `Nibble` is strictly zero in the upper
/// four bits, i.e. the identity `(x.get() & 0x0F) == x.get()`
/// holds for all `Nibble` values `x`.
///
/// Though the compiler doesn't _strictly_ guarantee it, you
/// may rely on the [null pointer optimisation](std::option#representation):
/// [`Option<Nibble>`](std::option) will have the same size
/// and alignment as `Nibble`. This also implies that you may
/// use `std::mem::transmute` from `Nibble` to `Option<Nibble>`,
/// and from `Some::<Nibble>(_)` to `Nibble`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Nibble(internal::UnsignedNibbleValue);

// CONVERSION TRAITS

nibble_try_from_impls!(
    u8,
    i8,
    std::num::NonZeroU8,
    u16,
    i16,
    u32,
    i32,
    u64,
    i64,
    u128,
    i128,
    usize,
    isize,
    char,
    bool
);

nibble_into_impls!(u8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize, char);

nibble_try_into_impls!(i8, std::num::NonZeroU8);

// DISPLAY TRAITS

nibble_fmt_impls!(
    std::fmt::Binary,
    std::fmt::Octal,
    std::fmt::LowerHex,
    std::fmt::UpperHex,
    std::fmt::Display,
    std::fmt::Debug
);

// CONSTANTS

nibble_constants!(
    MIN := 0,
    ZERO := 0,
    ONE := 1,
    TWO := 2,
    THREE := 3,
    FOUR := 4,
    FIVE := 5,
    SIX := 6,
    SEVEN := 7,
    EIGHT := 8,
    NINE := 9,
    TEN := 10,
    ELEVEN := 11,
    TWELVE := 12,
    THIRTEEN := 13,
    FOURTEEN := 14,
    FIFTEEN := 15,
    MAX := 15
);

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
                "the value {:#x} (created by {} << {}) cannot be represented as a nibble",
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
                "the value {:#x} (created by {} >> {}) cannot be represented as a nibble.",
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
    /// or returns `None` if it is greater than `15`.
    #[inline]
    pub const fn new(value: u8) -> Option<Self> {
        match Nibble::can_represent(value) {
            true => unsafe { Some(Nibble::new_unchecked(value)) },
            false => None,
        }
    }

    /// Consumes `self` and returns a `u8` representing its value, guaranteed
    /// to be at most 15.
    #[inline]
    pub const fn get(&self) -> u8 {
        self.0.get()
    }

    /// Converts a byte (`u8`) into a pair of nibbles, where
    /// the upper nibble is on the left and the lower nibble is
    /// on the right.
    ///
    /// ## Example
    /// ```
    /// use halfling::Nibble;
    ///
    /// let byte: u8 = 0x4A;
    /// let (upper, lower) = Nibble::pair_from_byte(byte);
    ///
    /// assert_eq!(upper.get(), 0x4);
    /// assert_eq!(lower.get(), 0xA);
    /// ```
    #[inline]
    pub const fn pair_from_byte(value: u8) -> (Self, Self) {
        let upper = unsafe { Self::new_unchecked(value >> 4) };
        let lower = unsafe { Self::new_unchecked(value & 0x0F) };
        (upper, lower)
    }

    /// Converts a pair of [`Nibble`] values into a byte, where the
    /// upper nibble is the first argument and the lower nibble is
    /// the second.
    ///
    /// ## Example
    /// ```
    /// use halfling::Nibble;
    ///
    /// let upper = Nibble::new(0xB).unwrap();
    /// let lower = Nibble::new(0x2).unwrap();
    /// let byte = Nibble::byte_from_pair(upper, lower);
    ///
    /// assert_eq!(byte, 0xB2);
    /// ```
    #[inline]
    pub const fn byte_from_pair(upper: Self, lower: Self) -> u8 {
        (upper.get() << 4) | lower.get()
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
            let nibble = Nibble::try_from(i).unwrap();
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
        let one = Nibble::ONE;
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
