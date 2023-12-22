use thiserror::Error;

/// The error produced when trying to convert
/// an unrepresentable integer into a [`Nibble`](crate::nibble::Nibble).
#[derive(Error, Debug)]
pub enum InvalidNibbleError {
    /// Occurs when attempting to construct a [`Nibble`](crate::nibble::Nibble) with
    /// a value larger than a byte.
    #[error("Attempted to construct a nibble representing 0b{0:b}.")]
    TooLarge(usize),
    /// Occurs when attempting to construct a [`Nibble`](crate::nibble::Nibble) with
    /// an unrepresentable byte, i.e. a byte whose upper 4 bits are not uniformly 0.
    #[error("Attempted to construct a nibble representing 0b{0:08b}, which has leading ones.")]
    UnrepresentableByte(u8),
}
