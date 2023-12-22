use crate::error::InvalidNibbleError;
use nonmax::NonMaxU8;

/// A byte-width unsigned nibble, i.e. an
/// integer from 0 (inclusive) up to 16 (exclusive).
///
/// While this type does not explicitly guarantee any
/// particular memory layout, it does guarantee that the
/// [null pointer optimization](std::option#representation)
/// applies.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Nibble(NonMaxU8);

impl TryFrom<u8> for Nibble {
    type Error = InvalidNibbleError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            nibble @ 0..=15 => Ok(Self(unsafe { NonMaxU8::new_unchecked(nibble) })),
            byte => Err(InvalidNibbleError::UnrepresentableByte(byte)),
        }
    }
}

impl TryFrom<usize> for Nibble {
    type Error = InvalidNibbleError;

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        if value > u8::MAX.into() {
            Err(InvalidNibbleError::TooLarge(value))
        } else {
            Nibble::try_from(u8::try_from(value).expect("value is byte-representable"))
        }
    }
}

impl Nibble {
    /// Constructs a new [`Nibble`] from the given value without
    /// checking that it is representable in 4 bits.
    ///
    /// # Safety
    /// The argument passed must be less than 16, i.e. it can be
    /// at most `0xf`/`0b1111`.
    pub unsafe fn new_unchecked(value: u8) -> Self {
        Self(NonMaxU8::new_unchecked(value))
    }

    /// Returns the value of `self` as a `u8`.
    pub fn get(&self) -> u8 {
        self.0.get()
    }
}
