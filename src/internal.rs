//! Utilities for implementing nibble types.
//!
//! # Bit Patterns
//! An [`UnsignedNibbleValue`] is defined such that its upper four bits
//! are always zero, and as such no particular effort needs to be taken
//! when showing its bit pattern to the user (i.e. in the [`std::fmt::Binary`]
//! implementation on [`Nibble`](crate::nibble::Nibble).
//!
//! In comparison, the [`SignedNibbleValue`] is just an enumeration of
//! all the values that a 4-bit two's complement signed integer *would* be
//! allowed to take; these values are stored as `i8`s, and as such both the
//! most and least significant bits have the potential to be set.
//!
//! # Conversions
//! Conversions between these two enums are handled by their `to_signed_value`
//! and `to_unsigned_value` functions respectively, which aren't given as [`From`]
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
    _Zero = 0x0,
    _One = 0x1,
    _Two = 0x2,
    _Three = 0x3,
    _Four = 0x4,
    _Five = 0x5,
    _Six = 0x6,
    _Seven = 0x7,
    _Eight = 0x8,
    _Nine = 0x9,
    _Ten = 0xa,
    _Eleven = 0xb,
    _Twelve = 0xc,
    _Thirteen = 0xd,
    _Fourteen = 0xe,
    _Fifteen = 0xf,
}

/// An enum of the allowed values of an [`I4`](crate::integer::I4),
/// using the bit patterns of an `i8` to simplify conversions between
/// the two.
///
/// Remember, the "4-bit" part of a nibble is
/// just an API niceity, rather than a strict
/// requirement. Here, we take advantage of the
/// full byte of memory to use [`std::mem::transmute`]
/// as much as possible, rather than defining some
/// arbitrary conversion schema from a [`Nibble`](crate::nibble::Nibble).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(i8)]
pub enum SignedNibbleValue {
    _NegativeEight = -8,
    _NegativeSeven = -7,
    _NegativeSix = -6,
    _NegativeFive = -5,
    _NegativeFour = -4,
    _NegativeThree = -3,
    _NegativeTwo = -2,
    _NegativeOne = -1,
    _Zero = 0,
    _One = 1,
    _Two = 2,
    _Three = 3,
    _Four = 4,
    _Five = 5,
    _Six = 6,
    _Seven = 7,
}

impl UnsignedNibbleValue {
    /// Consumes self and returns the corresponding [`SignedNibbleValue`]
    /// that it represents according to a 4-bit two's complement representation.
    #[inline]
    pub const fn to_signed_value(self) -> SignedNibbleValue {
        // extract byte and significand
        let mut byte = self as u8;
        let significand = byte >> 3;
        // set upper bits iff significand is 1
        byte |= significand * 0xF0;
        unsafe { std::mem::transmute(byte) }
    }
}

impl SignedNibbleValue {
    /// Consumes `self` and returns the [`UnsignedNibbleValue`] that corresponds
    /// to the underlying bit pattern of `self` according to a 4-bit two's complement
    /// representation.
    #[inline]
    pub const fn to_unsigned_value(self) -> UnsignedNibbleValue {
        // extract byte value and mask off upper bits
        unsafe { std::mem::transmute((self as i8) & 0x0F) }
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
    fn signed_nibble_value_is_byte_width() {
        assert_eq!(std::mem::size_of::<SignedNibbleValue>(), 1);
    }

    #[test]
    fn signed_nibble_value_to_unsigned_value_is_correct() {
        assert_eq!(
            SignedNibbleValue::_NegativeEight.to_unsigned_value(),
            UnsignedNibbleValue::_Eight
        );

        assert_eq!(
            SignedNibbleValue::_NegativeSeven.to_unsigned_value(),
            UnsignedNibbleValue::_Nine
        );

        assert_eq!(
            SignedNibbleValue::_NegativeSix.to_unsigned_value(),
            UnsignedNibbleValue::_Ten
        );

        assert_eq!(
            SignedNibbleValue::_NegativeFive.to_unsigned_value(),
            UnsignedNibbleValue::_Eleven
        );

        assert_eq!(
            SignedNibbleValue::_NegativeFour.to_unsigned_value(),
            UnsignedNibbleValue::_Twelve
        );

        assert_eq!(
            SignedNibbleValue::_NegativeThree.to_unsigned_value(),
            UnsignedNibbleValue::_Thirteen
        );

        assert_eq!(
            SignedNibbleValue::_NegativeTwo.to_unsigned_value(),
            UnsignedNibbleValue::_Fourteen
        );

        assert_eq!(
            SignedNibbleValue::_NegativeOne.to_unsigned_value(),
            UnsignedNibbleValue::_Fifteen
        );

        assert_eq!(
            SignedNibbleValue::_Zero.to_unsigned_value(),
            UnsignedNibbleValue::_Zero
        );

        assert_eq!(
            SignedNibbleValue::_One.to_unsigned_value(),
            UnsignedNibbleValue::_One
        );

        assert_eq!(
            SignedNibbleValue::_Two.to_unsigned_value(),
            UnsignedNibbleValue::_Two
        );

        assert_eq!(
            SignedNibbleValue::_Three.to_unsigned_value(),
            UnsignedNibbleValue::_Three
        );

        assert_eq!(
            SignedNibbleValue::_Four.to_unsigned_value(),
            UnsignedNibbleValue::_Four
        );

        assert_eq!(
            SignedNibbleValue::_Five.to_unsigned_value(),
            UnsignedNibbleValue::_Five
        );

        assert_eq!(
            SignedNibbleValue::_Six.to_unsigned_value(),
            UnsignedNibbleValue::_Six
        );

        assert_eq!(
            SignedNibbleValue::_Seven.to_unsigned_value(),
            UnsignedNibbleValue::_Seven
        );
    }

    #[test]
    fn unsigned_nibble_value_to_signed_value_is_correct() {
        assert_eq!(
            UnsignedNibbleValue::_Zero.to_signed_value(),
            SignedNibbleValue::_Zero
        );

        assert_eq!(
            UnsignedNibbleValue::_One.to_signed_value(),
            SignedNibbleValue::_One
        );

        assert_eq!(
            UnsignedNibbleValue::_Two.to_signed_value(),
            SignedNibbleValue::_Two
        );

        assert_eq!(
            UnsignedNibbleValue::_Three.to_signed_value(),
            SignedNibbleValue::_Three
        );

        assert_eq!(
            UnsignedNibbleValue::_Four.to_signed_value(),
            SignedNibbleValue::_Four
        );

        assert_eq!(
            UnsignedNibbleValue::_Five.to_signed_value(),
            SignedNibbleValue::_Five
        );

        assert_eq!(
            UnsignedNibbleValue::_Six.to_signed_value(),
            SignedNibbleValue::_Six
        );

        assert_eq!(
            UnsignedNibbleValue::_Seven.to_signed_value(),
            SignedNibbleValue::_Seven
        );

        assert_eq!(
            UnsignedNibbleValue::_Eight.to_signed_value(),
            SignedNibbleValue::_NegativeEight
        );

        assert_eq!(
            UnsignedNibbleValue::_Nine.to_signed_value(),
            SignedNibbleValue::_NegativeSeven
        );

        assert_eq!(
            UnsignedNibbleValue::_Ten.to_signed_value(),
            SignedNibbleValue::_NegativeSix
        );

        assert_eq!(
            UnsignedNibbleValue::_Eleven.to_signed_value(),
            SignedNibbleValue::_NegativeFive
        );

        assert_eq!(
            UnsignedNibbleValue::_Twelve.to_signed_value(),
            SignedNibbleValue::_NegativeFour
        );

        assert_eq!(
            UnsignedNibbleValue::_Thirteen.to_signed_value(),
            SignedNibbleValue::_NegativeThree
        );

        assert_eq!(
            UnsignedNibbleValue::_Fourteen.to_signed_value(),
            SignedNibbleValue::_NegativeTwo
        );

        assert_eq!(
            UnsignedNibbleValue::_Fifteen.to_signed_value(),
            SignedNibbleValue::_NegativeOne
        );
    }
}
