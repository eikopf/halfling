//! Utilities for implementing nibble types.
//!
//! # Bit Patterns
//! An [`UnsignedNibbleValue`] is defined such that its upper four bits
//! are always zero, and so no particular effort needs to be taken
//! when showing its bit pattern to the user (i.e. in the [`std::fmt::Binary`]
//! implementation on [`Nibble`](crate::nibble::Nibble).
//!
//! By comparison, the [`SignedNibbleValue`] is just an enumeration of
//! all the values that a 4-bit two's complement signed integer *would* be
//! allowed to take; these values are stored as `i8`s, and as such both the
//! most and least significant bits have the potential to be set.
//!
//! # Conversions
//! Conversions between these two enums are handled by their `signed_value`
//! and `unsigned_value` functions respectively, which aren't given as [`From`]
//! impls because they're `const`.
//!
//! Mapping an unsigned value to a signed one is simple, since it just corresponds
//! to masking off the upper four bits (proof by inspection).
//!
//! The reverse mapping is slightly more complicated, since we need to set the
//! upper 4 bits to `0xF` if the value is negative (i.e. the highest bit in the
//! nibble is `1`). This also needs to be a branchless operation, to avoid branch
//! misses on an operation as common as this one; remember that this needs to be
//! called every time a bitwise operation is applied to an [`I4`](crate::integer::I4).

/// The internal representation of a [`Nibble`](crate::nibble::Nibble),
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
    #[inline]
    pub const fn signed_value(self) -> i8 {
        // extract byte and significand
        let byte = self as u8;
        let significand = byte >> 3;
        // set upper bits iff significand is 1
        let int = byte | (significand * 0xF0);
        unsafe { std::mem::transmute(int) }
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
