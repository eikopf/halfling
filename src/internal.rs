//! Utilities for implementing nibble types.
//!
//! # Bit Patterns
//! An [`UnsignedNibbleValue`] is defined such that its upper four bits
//! are always zero, and so no particular effort needs to be taken
//! when showing its bit pattern to the user (i.e. in the [`std::fmt::Binary`]
//! implementation on [`Nibble`](crate::nibble::Nibble).
//!
//! # Conversions
//! While it's trivial to convert an [`UnsignedNibbleValue`] into a `u8`, the
//! conversion into an `i8` is less obvious; the bit pattern of a two's complement
//! signed integer depends significantly on its bitwidth.
//!
//! Mapping an unsigned value to a signed one is simple, since it just corresponds
//! to masking off the upper four bits (proof by inspection). The reverse mapping 
//! is slightly more complicated, since we need to set the upper 4 bits to `0xF` 
//! if the value is negative (i.e. the highest bit in the nibble is `1`). This 
//! should ideally also be branchless.[^1]
//!
//! [^1]: The algorithm described here appears to work for the conversion between
//! any `u2N` and `iN` (that is, conversion to a half-length signed integer from a
//! full length unsigned integer), due to the fact that the upper half of the
//! unsigned integer is uniformly identical to the leading bit of the lower half.

#![allow(dead_code)]

/// The internal representation of a [`Nibble`](crate::Nibble),
/// used to guarantee that the compiler can apply
/// niche value optimizations.
///
/// To avoid excessive branching, this enum must
/// be `repr(u8)` such that valid nibbles can be
/// directly created via [`std::mem::transmute`];
/// edge cases notwithstanding the variants in this
/// enum should never actually be constructed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum UnsignedNibbleValue {
    _0 = 0x0,
    _1 = 0x1,
    _2 = 0x2,
    _3 = 0x3,
    _4 = 0x4,
    _5 = 0x5,
    _6 = 0x6,
    _7 = 0x7,
    _8 = 0x8,
    _9 = 0x9,
    _A = 0xa,
    _B = 0xb,
    _C = 0xc,
    _D = 0xd,
    _E = 0xe,
    _F = 0xf,
}

impl UnsignedNibbleValue {
    /// Consumes self and returns the corresponding signed integer (as an `i8`)
    /// that it represents according to a 4-bit two's complement representation.
    ///
    /// This algorithm relies on the fact that for an "`i4`," its corresponding
    /// `i8` representation will have an upper nibble of either `0x0` or `0xF`,
    /// and this corresponds exactly to whether the significant of the `i4` is
    /// set.
    #[inline]
    pub const fn signed_value(self) -> i8 {
        // extract byte and significand
        let byte = self as u8;
        let significand = byte >> 3;
        // set upper bits iff significand is 1
        let int = byte | (significand * 0xF0);
        unsafe { std::mem::transmute(int) }
    }

    /// Consumes `self` and returns the corresponding `u8`.
    #[inline]
    pub const fn get(self) -> u8 {
        self as u8
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unsigned_nibble_value_is_byte_width() {
        assert_eq!(std::mem::size_of::<UnsignedNibbleValue>(), 1);
    }

    #[test]
    fn unsigned_nibble_value_to_signed_value_is_correct() {
        assert_eq!(
            UnsignedNibbleValue::_0.signed_value(),
            0
        );

        assert_eq!(
            UnsignedNibbleValue::_1.signed_value(),
            1
        );

        assert_eq!(
            UnsignedNibbleValue::_2.signed_value(),
            2
        );

        assert_eq!(
            UnsignedNibbleValue::_3.signed_value(),
            3
        );

        assert_eq!(
            UnsignedNibbleValue::_4.signed_value(),
            4
        );

        assert_eq!(
            UnsignedNibbleValue::_5.signed_value(),
            5
        );

        assert_eq!(
            UnsignedNibbleValue::_6.signed_value(),
            6
        );

        assert_eq!(
            UnsignedNibbleValue::_7.signed_value(),
            7
        );

        assert_eq!(
            UnsignedNibbleValue::_8.signed_value(),
            -8
        );

        assert_eq!(
            UnsignedNibbleValue::_9.signed_value(),
            -7
        );

        assert_eq!(
            UnsignedNibbleValue::_A.signed_value(),
            -6
        );

        assert_eq!(
            UnsignedNibbleValue::_B.signed_value(),
            -5
        );

        assert_eq!(
            UnsignedNibbleValue::_C.signed_value(),
            -4
        );

        assert_eq!(
            UnsignedNibbleValue::_D.signed_value(),
            -3
        );

        assert_eq!(
            UnsignedNibbleValue::_E.signed_value(),
            -2
        );

        assert_eq!(
            UnsignedNibbleValue::_F.signed_value(),
            -1
        );
    }
}
