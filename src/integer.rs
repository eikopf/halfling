use crate::{
    error::InvalidNibbleError,
    internal::{SignedNibbleValue, UnsignedNibbleValue},
    nibble::Nibble,
};

/// An unsigned integer backed by a [`Nibble`].
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct U4(UnsignedNibbleValue);

/// A signed integer backed by a [`Nibble`].
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct I4(SignedNibbleValue);

impl TryFrom<u8> for U4 {
    type Error = InvalidNibbleError<u8>;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        if value < 16 {
            Ok(unsafe { Self::new_unchecked(value) })
        } else {
            Err(InvalidNibbleError::Unrepresentable(value))
        }
    }
}

impl TryFrom<i8> for I4 {
    type Error = InvalidNibbleError<i8>;

    fn try_from(value: i8) -> Result<Self, Self::Error> {
        if value >= -8 && value <= 7 {
            Ok(unsafe { I4::new_unchecked(value) })
        } else {
            Err(InvalidNibbleError::Unrepresentable(value))
        }
    }
}

impl From<U4> for u8 {
    fn from(value: U4) -> Self {
        value.get()
    }
}

impl From<I4> for i8 {
    fn from(value: I4) -> Self {
        value.get()
    }
}

impl U4 {
    /// The minimum number of bits required to represent a [`U4`].
    ///
    /// As opposed to the primitive integer types, this value is not
    /// the same as `std::mem::sizeof<Nibble>() * 8`; instead it reflects
    /// the smallest possible size that a [`U4`] could be packed into.
    pub const BITS: u32 = Nibble::BITS;
    /// The minimum value representable by a [`U4`], which is 0.
    pub const MIN: U4 = unsafe { U4::new_unchecked(0) };
    /// The maximum value representable by a [`U4`], which is 15.
    pub const MAX: U4 = unsafe { U4::new_unchecked(15) };

    /// Constructs a new [`U4`] representing the given value
    /// without checking invariants.
    ///
    /// # Safety
    /// `value` must be strictly less than 16.
    #[inline]
    pub const unsafe fn new_unchecked(value: u8) -> Self {
        let nibble: UnsignedNibbleValue = std::mem::transmute(value);
        Self(nibble)
    }

    /// Consumes `self` and returns a `u8` representing its value, guaranteed
    /// to be at most 15.
    #[inline]
    pub const fn get(self) -> u8 {
        self.0 as u8
    }
}

impl I4 {
    /// The minimum number of bits required to represent a [`I4`].
    ///
    /// As opposed to the primitive integer types, this value is not
    /// the same as `std::mem::sizeof<Nibble>() * 8`; instead it reflects
    /// the smallest possible size that a [`I4`] could be packed into.
    pub const BITS: u32 = Nibble::BITS;
    /// The minimum value representable by a [`I4`], which is -8.
    pub const MIN: I4 = unsafe { I4::new_unchecked(-8) };
    /// The maximum value representable by a [`U4`], which is 7.
    pub const MAX: I4 = unsafe { I4::new_unchecked(7) };

    /// Constructs a new [`I4`] representing the given value without
    /// checking invariants.
    ///
    /// # Safety
    /// `value` must be between -8 (inclusive) and 7 (inclusive).
    #[inline]
    pub const unsafe fn new_unchecked(value: i8) -> Self {
        let nibble: SignedNibbleValue = std::mem::transmute(value);
        Self(nibble)
    }

    /// Consumes `self` and returns an `i8` representing its value, guaranteed
    /// to be at least -8 (inclusive) and at most 7 (inclusive).
    #[inline]
    pub fn get(self) -> i8 {
        self.0 as i8
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn u4_new_unchecked_converts_correctly() {
        for value in 0..=15u8 {
            let int: U4 = unsafe { U4::new_unchecked(value) };
            eprintln!("{}: {}", value, int.get());
            assert_eq!(value, int.get());
        }
    }

    #[test]
    fn i4_new_unchecked_converts_correctly() {
        for value in -8..=7i8 {
            let int: I4 = unsafe { I4::new_unchecked(value) };
            eprintln!("{}: {}", value, int.get());
            assert_eq!(value, int.get());
        }
    }

    #[test]
    fn u4_min_and_max_are_correct() {
        assert_eq!(U4::MIN.get(), 0u8);
        assert_eq!(U4::MAX.get(), 15u8)
    }

    #[test]
    fn i4_min_and_max_are_correct() {
        assert_eq!(I4::MIN.get(), -8i8);
        assert_eq!(I4::MAX.get(), 7i8)
    }

    #[test]
    fn size_of_option_u4_equals_size_of_u4() {
        assert_eq!(std::mem::size_of::<U4>(), std::mem::size_of::<Option<U4>>())
    }

    #[test]
    fn size_of_option_i4_equals_size_of_i4() {
        assert_eq!(std::mem::size_of::<I4>(), std::mem::size_of::<Option<I4>>())
    }
}
