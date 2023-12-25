
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
}
