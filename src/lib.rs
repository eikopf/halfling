//! # Halfling
//! Basic utilities and structures for handling nibbles, optimizing for memory usage whenever
//! possible.

// lints
#[warn(missing_docs)]
#[warn(clippy::missing_docs_in_private_items)]
#[warn(clippy::todo)]
#[warn(rustdoc::all)]
#[warn(clippy::missing_errors_doc)]
#[warn(clippy::missing_panics_doc)]
#[warn(clippy::missing_safety_doc)]

/// Byte-width nibbles.
pub mod nibble;

/// Error types.
pub mod error;

// TODOs
//mod packed_array;
//mod packed_vec;
