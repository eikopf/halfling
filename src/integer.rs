use crate::{
    error::{InvalidNibbleError, NibbleParseError},
    internal::{SignedNibbleValue, UnsignedNibbleValue},
    nibble::Nibble,
};

/// An unsigned integer backed by a nibble, representing a value from 0 to 15.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct U4(UnsignedNibbleValue);

/// A signed integer backed by a nibble, representing a value from -8 to 7.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct I4(SignedNibbleValue);

impl From<Nibble> for U4 {
    fn from(value: Nibble) -> Self {
        Self(value.unsigned_value())
    }
}

impl From<Nibble> for I4 {
    fn from(value: Nibble) -> Self {
        Self(value.unsigned_value().signed_value())
    }
}

impl From<U4> for Nibble {
    fn from(value: U4) -> Self {
        value.0.into()
    }
}

impl From<I4> for Nibble {
    fn from(value: I4) -> Self {
        value.0.unsigned_value().into()
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
        if (-8..=7).contains(&value) {
            Ok(unsafe { I4::new_unchecked(value) })
        } else {
            Err(InvalidNibbleError::Unrepresentable(value))
        }
    }
}

impl std::fmt::Binary for U4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let nibble: Nibble = (*self).into();
        <Nibble as std::fmt::Binary>::fmt(&nibble, f)
    }
}

impl std::fmt::Binary for I4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let nibble: Nibble = (*self).into();
        <Nibble as std::fmt::Binary>::fmt(&nibble, f)
    }
}

impl std::fmt::Octal for U4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let nibble: Nibble = (*self).into();
        <Nibble as std::fmt::Octal>::fmt(&nibble, f)
    }
}

impl std::fmt::Octal for I4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let nibble: Nibble = (*self).into();
        <Nibble as std::fmt::Octal>::fmt(&nibble, f)
    }
}

impl std::fmt::LowerHex for U4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let nibble: Nibble = (*self).into();
        <Nibble as std::fmt::LowerHex>::fmt(&nibble, f)
    }
}

impl std::fmt::LowerHex for I4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let nibble: Nibble = (*self).into();
        <Nibble as std::fmt::LowerHex>::fmt(&nibble, f)
    }
}

impl std::fmt::UpperHex for U4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let nibble: Nibble = (*self).into();
        <Nibble as std::fmt::UpperHex>::fmt(&nibble, f)
    }
}

impl std::fmt::UpperHex for I4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let nibble: Nibble = (*self).into();
        <Nibble as std::fmt::UpperHex>::fmt(&nibble, f)
    }
}

impl std::fmt::Display for U4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <u8 as std::fmt::Display>::fmt(&self.get(), f)
    }
}

impl std::fmt::Display for I4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <i8 as std::fmt::Display>::fmt(&self.get(), f)
    }
}

impl std::ops::Add for U4 {
    type Output = U4;

    fn add(self, rhs: Self) -> Self::Output {
        let sum: u8 = self.get() + rhs.get();
        match Self::try_from(sum) {
            Ok(u4) => u4,
            Err(_) => panic!(
                "Tried to represent {} + {} ({}) with a halfling::integer::U4",
                self.get(),
                rhs.get(),
                sum
            ),
        }
    }
}

impl std::ops::Add for I4 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let sum: i8 = self.get() + rhs.get();
        match Self::try_from(sum) {
            Ok(i4) => i4,
            Err(_) => panic!(
                "Tried to represent {} + {} ({}) with a halfling::integer::I4",
                self.get(),
                rhs.get(),
                sum
            ),
        }
    }
}

impl std::ops::AddAssign for U4 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl std::ops::AddAssign for I4 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl std::ops::BitAnd for U4 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        // get nibble representations
        let lhs: Nibble = self.into();
        let rhs: Nibble = rhs.into();
        // defer to the BitAnd impl on Nibble
        (lhs & rhs).into()
    }
}

impl std::ops::BitAnd for I4 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        // get nibble representations
        let lhs: Nibble = self.into();
        let rhs: Nibble = rhs.into();
        // defer to the BitAnd impl on Nibble
        (lhs & rhs).into()
    }
}

impl std::ops::BitAndAssign for U4 {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl std::ops::BitAndAssign for I4 {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl std::ops::BitOr for U4 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        let lhs: Nibble = self.into();
        let rhs: Nibble = rhs.into();
        (lhs | rhs).into()
    }
}

impl std::ops::BitOr for I4 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        let lhs: Nibble = self.into();
        let rhs: Nibble = rhs.into();
        (lhs | rhs).into()
    }
}

impl std::ops::BitOrAssign for U4 {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl std::ops::BitOrAssign for I4 {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl std::ops::BitXor for U4 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        let lhs: Nibble = self.into();
        let rhs: Nibble = rhs.into();
        (lhs ^ rhs).into()
    }
}

impl std::ops::BitXor for I4 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        let lhs: Nibble = self.into();
        let rhs: Nibble = rhs.into();
        (lhs ^ rhs).into()
    }
}

impl std::ops::BitXorAssign for U4 {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}

impl std::ops::BitXorAssign for I4 {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}

impl std::ops::Div for U4 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        let quot = self.get() / rhs.get();
        match Self::try_from(quot) {
            Ok(result) => result,
            Err(_) => panic!(
                "Tried to represent {} / {} ({}) with a halfling::integer::U4",
                self.get(),
                rhs.get(),
                quot
            ),
        }
    }
}

impl std::ops::Div for I4 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        let quot = self.get() / rhs.get();
        match Self::try_from(quot) {
            Ok(result) => result,
            Err(_) => panic!(
                "Tried to represent {} / {} ({}) with a halfling::integer::I4",
                self.get(),
                rhs.get(),
                quot
            ),
        }
    }
}

impl std::ops::DivAssign for U4 {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl std::ops::DivAssign for I4 {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl std::ops::Mul for U4 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let prod: u8 = self.get() * rhs.get();
        match Self::try_from(prod) {
            Ok(u4) => u4,
            Err(_) => panic!(
                "Tried to represent {} * {} ({}) with a halfling::integer::U4",
                self.get(),
                rhs.get(),
                prod
            ),
        }
    }
}

impl std::ops::Mul for I4 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let prod: i8 = self.get() * rhs.get();
        match Self::try_from(prod) {
            Ok(i4) => i4,
            Err(_) => panic!(
                "Tried to represent {} * {} ({}) with a halfling::integer::I4",
                self.get(),
                rhs.get(),
                prod
            ),
        }
    }
}

impl std::ops::MulAssign for U4 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl std::ops::MulAssign for I4 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl std::ops::Neg for I4 {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let value = -(self.get());
        match Self::try_from(value) {
            Ok(i4) => i4,
            Err(_) => panic!("Tried to represent {} in a halfling::integer::I4", value),
        }
    }
}

impl std::ops::Not for U4 {
    type Output= Self;

    fn not(self) -> Self::Output {
        let nibble: Nibble = self.into();
        (!nibble).into()
    }
}

impl std::ops::Not for I4 {
    type Output= Self;

    fn not(self) -> Self::Output {
        let nibble: Nibble = self.into();
        (!nibble).into()
    }
}

impl std::ops::Rem for U4 {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        let residue = self.get() % rhs.get();
        match Self::try_from(residue) {
            Ok(result) => result,
            Err(_) => panic!(
                "Tried to represent {} % {} ({}) with a halfling::integer::U4",
                self.get(),
                rhs.get(),
                residue
            ),
        }
    }
}

impl std::ops::Rem for I4 {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        let residue = self.get() % rhs.get();
        match Self::try_from(residue) {
            Ok(result) => result,
            Err(_) => panic!(
                "Tried to represent {} % {} ({}) with a halfling::integer::I4",
                self.get(),
                rhs.get(),
                residue
            ),
        }
    }
}

impl std::ops::RemAssign for U4 {
    fn rem_assign(&mut self, rhs: Self) {
        *self = *self % rhs;
    }
}

impl std::ops::RemAssign for I4 {
    fn rem_assign(&mut self, rhs: Self) {
        *self = *self % rhs;
    }
}

impl std::ops::Sub for U4 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        let diff = self.get() - rhs.get();
        match Self::try_from(diff) {
            Ok(result) => result,
            Err(_) => panic!(
                "Tried to represent {} - {} ({}) with a halfling::integer::U4",
                self.get(),
                rhs.get(),
                diff
            ),
        }
    }
}

impl std::ops::Sub for I4 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        let diff = self.get() - rhs.get();
        match Self::try_from(diff) {
            Ok(result) => result,
            Err(_) => panic!(
                "Tried to represent {} - {} ({}) with a halfling::integer::I4",
                self.get(),
                rhs.get(),
                diff
            ),
        }
    }
}

impl std::ops::SubAssign for U4 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl std::ops::SubAssign for I4 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl num_traits::Unsigned for U4 {}

impl num_traits::Signed for I4 {
    fn abs(&self) -> Self {
        // this behaviour matches the release behaviour of
        // the abs function on primitive signed integers, and
        // the expected behavior for num::Unsigned types
        self.get().abs().try_into().unwrap_or(I4::MIN)
    }

    fn abs_sub(&self, other: &Self) -> Self {
        let value = i8::abs_sub(&self.get(), &other.get());
        match Self::try_from(value) {
            Ok(i4) => i4,
            Err(_) => {
                panic!(
                    "Tried to represent i8::abs_sub(&{}, &{}) ({}) with a halfling::integer::I4",
                    self.get(),
                    other.get(),
                    value
                )
            }
        }
    }

    fn signum(&self) -> Self {
        self.get().signum().try_into().expect("0, 1, and -1 are valid nibbles")
    }

    fn is_positive(&self) -> bool {
        self.get().is_positive()
    }

    fn is_negative(&self) -> bool {
        self.get().is_negative()
    }
}

impl num_traits::Bounded for U4 {
    fn min_value() -> Self {
        Self::MIN
    }

    fn max_value() -> Self {
        Self::MAX
    }
}

impl num_traits::Bounded for I4 {
    fn min_value() -> Self {
        Self::MIN
    }

    fn max_value() -> Self {
        Self::MAX
    }
}

impl num_traits::Num for U4 {
    type FromStrRadixErr = NibbleParseError<u8>;

    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        u8::from_str_radix(str, radix)
            .map_err(NibbleParseError::ParseError)
            .map(Self::try_from)?
            .map_err(NibbleParseError::ValueError)
    }
}

impl num_traits::Num for I4 {
    type FromStrRadixErr = NibbleParseError<i8>;

    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        i8::from_str_radix(str, radix)
            .map_err(NibbleParseError::ParseError)
            .map(Self::try_from)?
            .map_err(NibbleParseError::ValueError)
    }
}

impl num_traits::One for U4 {
    fn one() -> Self {
        unsafe { Self::new_unchecked(1) }
    }

    fn is_one(&self) -> bool
    where
        Self: PartialEq,
    {
        self.0 == UnsignedNibbleValue::_One
    }
}

impl num_traits::One for I4 {
    fn one() -> Self {
        unsafe { Self::new_unchecked(1) }
    }

    fn is_one(&self) -> bool
    where
        Self: PartialEq,
    {
        self.0 == SignedNibbleValue::_One
    }
}

impl num_traits::Zero for U4 {
    fn zero() -> Self {
        Self::MIN
    }

    fn is_zero(&self) -> bool {
        self.0 == UnsignedNibbleValue::_Zero
    }
}

impl num_traits::Zero for I4 {
    fn zero() -> Self {
        unsafe { I4::new_unchecked(0) }
    }

    fn is_zero(&self) -> bool {
        self.0 == SignedNibbleValue::_Zero
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
