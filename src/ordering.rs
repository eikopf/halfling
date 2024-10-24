//! Well-defined orderings for the two [`Nibble`] values in a `u8`.

use crate::Nibble;

/// An ordering for the two [`Nibble`] values in a `u8`.
///
/// For a given `byte: u8`, its lower nibble is given by `x & 0xF0`, and its
/// upper nibble is given by `x >> 4`. The choice of ordering can be seen as
/// analogous to endianness.
///
/// Actually, this *is* endianness. Because it's not a well-defined term, we
/// are free to use little-endian and big-endian to describe the two possible
/// nibble orderings; the corresponding implementors are [`Le`] and [`Be`].
pub trait Ordering {
    /// Splits a `byte` into two [`Nibble`] values such that they are ordered
    /// from left-to-right.
    fn split_byte(byte: u8) -> (Nibble, Nibble);

    /// Combines `first` and `second` into a single `u8` according to the
    /// ordering defined by the implementor.
    fn join_nibbles(first: Nibble, second: Nibble) -> u8;
}

/// The little-endian [`Nibble`] [`Ordering`] marker.
pub struct Le;

impl Ordering for Le {
    #[inline]
    fn split_byte(byte: u8) -> (Nibble, Nibble) {
        let (upper, lower) = Nibble::pair_from_byte(byte);
        (lower, upper)
    }

    #[inline]
    fn join_nibbles(first: Nibble, second: Nibble) -> u8 {
        let lower = first.get();
        let upper = second.get() << 4;
        upper | lower
    }
}

/// The big-endian [`Nibble`] [`Ordering`] marker.
pub struct Be;

impl Ordering for Be {
    #[inline]
    fn split_byte(byte: u8) -> (Nibble, Nibble) {
        let (upper, lower) = Nibble::pair_from_byte(byte);
        (upper, lower)
    }

    #[inline]
    fn join_nibbles(first: Nibble, second: Nibble) -> u8 {
        let lower = second.get();
        let upper = first.get() << 4;
        upper | lower
    }
}
