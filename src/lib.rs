//! Basic utilities and structures for handling nibbles.
//!
//! # Nibbles
//! A [nibble](https://en.wikipedia.org/wiki/Nibble) (sometimes also *nybble*
//! or *nybl*) is a 4-bit unit of data, equivalent in size to a single-digit
//! hexadecimal number.
//!
//! Historically, nibbles were used in early computers to represent small
//! enumerations, e.g. the individual digits of a base-10 number, but today
//! they are largely API details (as opposed to genuinely necessary
//! memory-saving constructs).
//!
//! `halfling`'s [`Nibble`] is a byte-width struct containing a single nibble,
//! which guarantees that the
//! [niche value optimization](core::option#representation) will apply
//! (a [`Nibble`] has 4 unused bits, and hence 240 such niches are available).
//! They are byte-width due to [Rust's fundamental expectation that types are
//! byte-aligned](https://doc.rust-lang.org/reference/type-layout.html), which
//! prevents us from constructing a single type that genuinely consumes only a
//! nibble of memory.
//!
//! # Ordering Nibbles
//! When representing larger units of data in terms of bytes, we need to agree
//! on the "correct" order of the bytes. The two most-common representations
//! are little-endian (LE) and big-endian (BE), which define the first byte to
//! be the least and most significant byte respectively.
//!
//! Similarly, a byte can be divided into two [`Nibble`] values in two ways,
//! depending on whether the least-significant nibble is first or second. The
//! unit structs [`Le`] and [`Be`] provide implementations of the [`Ordering`]
//! trait for these two orderings, and are used to control the order in which
//! a [`Nibbles`] iterator produces values.

#![cfg_attr(not(any(feature = "std", test)), no_std)]
#![warn(missing_docs)]
#![warn(rustdoc::all)]
#![warn(clippy::all)]

use ordering::{Be, Le, Ordering};
use thiserror::Error;

#[macro_use]
mod internal;

pub mod ordering;

#[derive(Debug, Clone)]
/// A [`Nibble`] iterator over a `T: impl Iterator<Item=u8>` with [`Ordering`]
/// defined by `O`.
pub struct Nibbles<T, O> {
    bytes: T,
    next: Option<Nibble>,
    ordering: core::marker::PhantomData<O>,
}

impl<T> Nibbles<T, Le> {
    /// Constructs a new [`Nibbles`] iterating over the nibbles of `bytes` in
    /// little-endian order.
    pub fn le<U>(bytes: U) -> Self
    where
        U: IntoIterator<IntoIter = T>,
    {
        Nibbles {
            bytes: <U as IntoIterator>::into_iter(bytes),
            next: None,
            ordering: core::marker::PhantomData,
        }
    }
}

impl<T> Nibbles<T, Be> {
    /// Constructs a new [`Nibbles`] iterating over the nibbles of `bytes` in
    /// big-endian order.
    pub fn be<U>(bytes: U) -> Self
    where
        U: IntoIterator<IntoIter = T>,
    {
        Nibbles {
            bytes: <U as IntoIterator>::into_iter(bytes),
            next: None,
            ordering: core::marker::PhantomData,
        }
    }
}

impl<T: Iterator<Item = u8>, O: Ordering> Iterator for Nibbles<T, O> {
    type Item = Nibble;

    fn next(&mut self) -> Option<Self::Item> {
        self.next.take().or_else(|| {
            self.bytes.next().map(|byte| {
                let (first, second) = O::split_byte(byte);
                self.next = Some(second);
                first
            })
        })
    }
}

/// The error produced if a conversion from an integral type to a [`Nibble`]
/// fails. The [`0`](NibbleTryFromIntError::0) field contains the value which
/// could not be converted to a [`Nibble`].
#[derive(Debug, Error)]
#[error("failed to convert {0:?} into a nibble.")]
pub struct NibbleTryFromIntError<T>(pub T);

/// A byte-width nibble, representing a 4-bit unit of data.
///
/// # Memory Layout
/// The bit pattern of a `Nibble` is strictly zero in the upper
/// four bits, i.e. the identity `(x.get() & 0x0F) == x.get()`
/// holds for all `Nibble` values `x`.
///
/// Though the compiler doesn't _strictly_ guarantee it, you
/// may rely on the [null pointer optimisation](core::option#representation):
/// [`Option<Nibble>`](core::option) will have the same size
/// and alignment as `Nibble`. This also implies that you may
/// use `core::mem::transmute` to send `Nibble` to `Option<Nibble>`,
/// and to send `Some::<Nibble>(_)` to `Nibble`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Nibble(internal::UnsignedNibbleValue);

// CONVERSION TRAITS

nibble_try_from_impls!(
    u8,
    i8,
    core::num::NonZeroU8,
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

nibble_into_impls!(
    u8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize, char
);

nibble_try_into_impls!(i8, core::num::NonZeroU8);

// DISPLAY TRAITS

nibble_fmt_impls!(
    core::fmt::Binary,
    core::fmt::Octal,
    core::fmt::LowerHex,
    core::fmt::UpperHex,
    core::fmt::Display,
    core::fmt::Debug
);

// CONSTANTS

nibble_constants!(
    ALL_UNSET := 0,
    ZERO := 0,
    ONE := 1,
    TWO := 2,
    FOUR := 4,
    EIGHT := 8,
    ALL_SET := 15
);

// OPERATOR TRAITS
//
// Recall that a Nibble is _not_ an integer in the semantic sense, just a 4-bit
// set. We can only implement traits that make sense from this perspective, so
// mostly only the Bit{op} traits.
//
// The BitAnd, BitOr, and BitXor traits (as well as their Assign variants) are
// morally closed functions in the sense that they cannot reasonably be
// implemented in a way that produces a u8 greater than 15. This is similarly
// true for the Not trait.
//
// However, the Shr and Shl traits (along with their Assign counterparts) are
// more complicated. We'll want to write impls both for when Nibble is the Self
// type and when it is the rhs argument; because this is coherent for many
// integer types we will need to write this as a macro.

impl core::ops::BitAnd for Nibble {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        let left: u8 = self.get();
        let right: u8 = rhs.get();

        // upper bits are all zero,
        // so no need to mask them off
        let result: u8 = left & right;
        unsafe { Nibble::new_unchecked(result) }
    }
}

impl core::ops::BitAndAssign for Nibble {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl core::ops::BitOr for Nibble {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        let left: u8 = self.get();
        let right: u8 = rhs.get();

        // the upper 4 bits are all zero,
        // so no need to mask them off.
        let result = left | right;
        unsafe { Nibble::new_unchecked(result) }
    }
}

impl core::ops::BitOrAssign for Nibble {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl core::ops::BitXor for Nibble {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        let left: u8 = self.get();
        let right: u8 = rhs.get();
        let result = left ^ right;
        unsafe { Nibble::new_unchecked(result) }
    }
}

impl core::ops::BitXorAssign for Nibble {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}

impl core::ops::Not for Nibble {
    type Output = Self;

    fn not(self) -> Self::Output {
        let value: u8 = self.get();
        let result: u8 = !value & 0x0F;
        unsafe { Nibble::new_unchecked(result) }
    }
}

// BITSHIFT OPERATOR IMPLS

nibble_rhs_bitshift_impls! {
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize
}

nibble_bitshift_impls! {
    Nibble,
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize
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
        unsafe { core::mem::transmute(value) }
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
    #[inline]
    pub(crate) const fn pair_from_byte(value: u8) -> (Self, Self) {
        let upper = unsafe { Self::new_unchecked(value >> 4) };
        let lower = unsafe { Self::new_unchecked(value & Self::BYTE_MASK) };
        (upper, lower)
    }

    /// Checks whether the given `u8` can be safely converted into a [`Nibble`].
    ///
    /// Prefer using this check over an ad-hoc implementation before making
    /// calls to `Nibble::new_unchecked`, since it is faster than the naive
    /// `x < 16`.
    #[inline]
    pub const fn can_represent(value: u8) -> bool {
        (value & 0xF0) == 0x00
    }

    /// For all `x: u8`, `x & Nibble::BYTE_MASK` is a valid Nibble.
    pub(crate) const BYTE_MASK: u8 = 0x0F;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn size_of_option_nibble_equals_size_of_nibble() {
        assert_eq!(
            core::mem::size_of::<Option<Nibble>>(),
            core::mem::size_of::<Nibble>()
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
            assert!(nibble.get() + complement.get() == 15u8);
        }
    }

    #[test]
    fn shl_produces_correct_values() {
        let one = Nibble::ONE;
        let two = one << 1u8;
        let four = one << 2u32;
        let eight = one << 3isize;

        assert_eq!(one.get(), 0b0001);
        assert_eq!(two.get(), 0b0010);
        assert_eq!(four.get(), 0b0100);
        assert_eq!(eight.get(), 0b1000);
    }

    #[test]
    fn shr_produces_correct_values() {
        let fifteen = Nibble::try_from(15u8).unwrap();
        let seven = fifteen >> 1usize;
        let three = fifteen >> 2i128;
        let one = fifteen >> 3i8;

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

    #[test]
    fn correct_nibbles_iteration_order() {
        let bytes = [0xA6, 0x3D, 0x47];

        let mut le = Nibbles::le(bytes).map(|x| x.get());
        let mut be = Nibbles::be(bytes).map(|x| x.get());

        assert_eq!(le.next(), Some(0x6));
        assert_eq!(le.next(), Some(0xA));
        assert_eq!(le.next(), Some(0xD));
        assert_eq!(le.next(), Some(0x3));
        assert_eq!(le.next(), Some(0x7));
        assert_eq!(le.next(), Some(0x4));

        assert_eq!(be.next(), Some(0xA));
        assert_eq!(be.next(), Some(0x6));
        assert_eq!(be.next(), Some(0x3));
        assert_eq!(be.next(), Some(0xD));
        assert_eq!(be.next(), Some(0x4));
        assert_eq!(be.next(), Some(0x7));
    }

    #[test]
    fn nibbles_constructor_apis_behave_correctly() {
        let bytes: Vec<u8> = vec![0x32, 0x0C, 0x1F];

        // first iterate by a reference to bytes
        for nybl in Nibbles::le(bytes.iter().copied()) {
            dbg![nybl];
        }

        // then consume the vector and iterate
        for nybl in Nibbles::be(bytes) {
            dbg![nybl];
        }
    }
}
