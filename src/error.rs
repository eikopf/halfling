use thiserror::Error;

/// The error produced when trying to convert
/// an unrepresentable integer into a [`Nibble`](crate::nibble::Nibble).
#[derive(Debug, Error)]
pub enum InvalidNibbleError<Src: num::Num> {
    /// Occurs when attempting to construct a [`Nibble`](crate::nibble::Nibble) with
    /// a value larger than a byte.
    #[error("Attempted to construct a nibble representing a value larger than a byte.")]
    TooLarge(Src),
    /// Occurs when attempting to construct a [`Nibble`](crate::nibble::Nibble) with
    /// an unrepresentable byte, i.e. a byte whose upper 4 bits are not uniformly 0.
    #[error("Attempted to construct a nibble representing 0b{0:08b}.")]
    Unrepresentable(Src),
}

/// The error produced by the `from_str_radix` methods on
/// both [`U4`](crate::integer::U4) and [`I4`](crate::integer::I4).
#[derive(Debug, Error)]
pub enum NibbleParseError<Src: num::Num> {
    /// Occurs if a string cannot be parsed into the `Src` type.
    ParseError(std::num::ParseIntError),
    /// Occurs if the target type cannot represent a given value,
    ValueError(InvalidNibbleError<Src>),
}
