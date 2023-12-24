use crate::error::InvalidNibbleError;
use num_enum::{IntoPrimitive, UnsafeFromPrimitive};

/// The internal representation of a [`Nibble`],
/// used to guarantee that the compiler can apply
/// niche value optimizations.
///
/// To avoid excessive branching, this enum must
/// be `repr(u8)` such that valid nibbles can be
/// directly created via [`std::mem::transmute`];
/// the actual details are mediated by the
/// [`num_enum`] crate. Edge cases notwithstanding,
/// the variants in this enum should never actually
/// be constructed.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, UnsafeFromPrimitive, IntoPrimitive,
)]
#[repr(u8)]
enum AllowedNibbleValue {
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

/// A byte-width unsigned nibble, i.e. an
/// integer from 0 (inclusive) up to 16 (exclusive).
///
/// While this type does not explicitly guarantee any
/// particular memory layout, it does guarantee that the
/// [null pointer optimization](std::option#representation)
/// applies: [`Option<Nibble>`](std::option) will always have the same size
/// and alignment as `Nibble`
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Nibble(AllowedNibbleValue);

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

impl std::ops::Not for Nibble {
    type Output = Self;

    fn not(self) -> Self::Output {
        let value: u8 = self.into();
        let mask: u8 = 0b00001111;

        // a bitwise not will flip the upper four bits
        // to ones, so we mask them off.
        let complement: u8 = !value & mask;
        unsafe { std::mem::transmute(complement) }
    }
}

impl From<Nibble> for u8 {
    fn from(value: Nibble) -> Self {
        unsafe { std::mem::transmute(value) }
    }
}

impl TryFrom<u8> for Nibble {
    type Error = InvalidNibbleError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0..=15 => Ok(Nibble(unsafe {
                AllowedNibbleValue::unchecked_transmute_from(value)
            })),
            _ => Err(InvalidNibbleError::UnrepresentableByte(value)),
        }
    }
}

impl TryFrom<usize> for Nibble {
    type Error = InvalidNibbleError;

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        if value > u8::MAX.into() {
            Err(InvalidNibbleError::TooLarge(value))
        } else {
            Nibble::try_from(u8::try_from(value).unwrap())
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
    /// The minimum value representable by a nibble, whose bit pattern is `0b0000`.
    pub const MIN: Nibble = unsafe { Nibble::new_unchecked(0b0000) };
    /// The maximum value representable by a nibble, whose bit pattern is `0b1111`.
    pub const MAX: Nibble = unsafe { Nibble::new_unchecked(0b1111) };

    /// Constructs a new nibble representing the given value
    /// without checking invariants.
    ///
    /// # Safety
    /// `value` must be strictly less than 16.
    pub const unsafe fn new_unchecked(value: u8) -> Self {
        debug_assert!(value < 16);
        std::mem::transmute(value)
    }

    /// Consumes `self` and returns a `u8` representing its value, guaranteed
    /// to be at most 15.
    pub const fn get(self) -> u8 {
        unsafe { std::mem::transmute(self) }
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
        for i in 0..=15 {
            let nibble: u8 = i.try_into().unwrap();
            unsafe {
                assert_eq!(
                    nibble,
                    AllowedNibbleValue::unchecked_transmute_from(nibble).into()
                );
            }
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
}
