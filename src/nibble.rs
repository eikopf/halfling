use crate::{error::InvalidNibbleError, internal::UnsignedNibbleValue};

/// A byte-width nibble, representing a 4-bit unit of data.
///
/// While this type does not explicitly guarantee any
/// particular memory layout, it does guarantee that the
/// [null pointer optimization](std::option#representation)
/// applies: [`Option<Nibble>`](std::option) will always have the same size
/// and alignment as `Nibble`
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct Nibble(pub(crate) UnsignedNibbleValue);

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

impl std::ops::BitAnd for Nibble {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        let left: u8 = self.into();
        let right: u8 = rhs.into();

        // upper bits are all zero,
        // so no need to mask them off
        let result: u8 = left & right;
        unsafe { Nibble::new_unchecked(result) }
    }
}

impl std::ops::BitAndAssign for Nibble {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl std::ops::BitOr for Nibble {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        let left: u8 = self.into();
        let right: u8 = rhs.into();

        // the upper 4 bits are all zero,
        // so no need to mask them off.
        let result = left | right;
        unsafe { Nibble::new_unchecked(result) }
    }
}

impl std::ops::BitOrAssign for Nibble {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl std::ops::BitXor for Nibble {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        let left: u8 = self.into();
        let right: u8 = rhs.into();
        let result = left ^ right;
        unsafe { Nibble::new_unchecked(result) }
    }
}

impl std::ops::BitXorAssign for Nibble {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}

impl std::ops::Not for Nibble {
    type Output = Self;

    fn not(self) -> Self::Output {
        let value: u8 = self.into();
        let mask: u8 = 0b00001111;

        // a bitwise not will flip the upper four bits
        // to ones, so we mask them off.
        let result: u8 = !value & mask;
        unsafe { Nibble::new_unchecked(result) }
    }
}

impl std::ops::Shl<u8> for Nibble {
    type Output = Nibble;

    fn shl(self, rhs: u8) -> Self::Output {
        let lhs: u8 = self.into();
        let result = lhs << rhs;

        match Nibble::try_from(result) {
            Ok(nibble) => nibble,
            Err(_) => panic!(
                "The value {:#x} created by {} << {} cannot be represented as a nibble.",
                result, lhs, rhs
            ),
        }
    }
}

impl std::ops::ShlAssign<u8> for Nibble {
    fn shl_assign(&mut self, rhs: u8) {
        *self = *self << rhs;
    }
}

impl std::ops::Shr<u8> for Nibble {
    type Output = Nibble;

    fn shr(self, rhs: u8) -> Self::Output {
        let lhs: u8 = self.into();
        let result = lhs >> rhs;

        match Nibble::try_from(result) {
            Ok(nibble) => nibble,
            Err(_) => panic!(
                "The value {:#x} created by {} >> {} cannot be represented as a nibble.",
                result, lhs, rhs
            ),
        }
    }
}

impl std::ops::ShrAssign<u8> for Nibble {
    fn shr_assign(&mut self, rhs: u8) {
        *self = *self >> rhs;
    }
}

impl From<Nibble> for u8 {
    fn from(value: Nibble) -> Self {
        unsafe { std::mem::transmute(value) }
    }
}

impl TryFrom<u8> for Nibble {
    type Error = InvalidNibbleError<u8>;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0..=15 => Ok(unsafe { Nibble::new_unchecked(value) }),
            _ => Err(InvalidNibbleError::Unrepresentable(value)),
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

    /// Constructs a new nibble representing the given value
    /// without checking invariants.
    ///
    /// # Safety
    /// `value` must be strictly less than 16.
    #[inline]
    pub const unsafe fn new_unchecked(value: u8) -> Self {
        debug_assert!(value < 16);
        std::mem::transmute(value)
    }

    /// Consumes `self` and returns a `u8` representing its value, guaranteed
    /// to be at most 15.
    #[inline]
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
        for i in 0..=15u8 {
            let nibble: Nibble = unsafe { Nibble::new_unchecked(i) };
            assert_eq!(nibble.get(), i);
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

    #[test]
    fn shl_produces_correct_values() {
        let one = Nibble::try_from(1u8).unwrap();
        let two = one << 1;
        let four = one << 2;
        let eight = one << 3;

        assert_eq!(one.get(), 0b0001);
        assert_eq!(two.get(), 0b0010);
        assert_eq!(four.get(), 0b0100);
        assert_eq!(eight.get(), 0b1000);
    }

    #[test]
    fn shr_produces_correct_values() {
        let fifteen = Nibble::try_from(15u8).unwrap();
        let seven = fifteen >> 1;
        let three = fifteen >> 2;
        let one = fifteen >> 3;

        assert_eq!(fifteen.get(), 0b1111);
        assert_eq!(seven.get(), 0b0111);
        assert_eq!(three.get(), 0b0011);
        assert_eq!(one.get(), 0b0001);
    }
}
