use crate::nibble::Nibble;

/// An unsigned integer backed by a [`Nibble`].
pub struct U4(Nibble);

/// A signed integer backed by a [`Nibble`].
pub struct I4(Nibble);

impl From<Nibble> for U4 {
    fn from(value: Nibble) -> Self {
        Self(value)
    }
}

impl From<Nibble> for I4 {
    fn from(value: Nibble) -> Self {
        Self(value)
    }
}

impl From<U4> for Nibble {
    fn from(value: U4) -> Self {
        value.0
    }
}

impl From<I4> for Nibble {
    fn from(value: I4) -> Self {
        value.0
    }
}

impl U4 {
    /// The minimum value representable by a [`U4`], which is 0.
    pub const MIN: U4 = U4(Nibble::MIN);
    /// The maximum value representable by a [`U4`], which is 15.
    pub const MAX: U4 = U4(Nibble::MAX);
}
