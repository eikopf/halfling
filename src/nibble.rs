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
/// [`num_enum`] crate.
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
/// applies.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Nibble(AllowedNibbleValue);

impl From<Nibble> for u8 {
    fn from(value: Nibble) -> Self {
        value.0.into()
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
    /// Constructs a new nibble representing the given value
    /// without checking invariants.
    ///
    /// # Safety
    /// `value` must be strictly less than 16.
    pub const unsafe fn new_unchecked(value: u8) -> Self {
        debug_assert!(value < 16);
        std::mem::transmute(value)
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
    fn representable_nibbles_transmute_correctly() {
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
}
