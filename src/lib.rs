//! Basic utilities and structures for handling nibbles, optimizing for memory usage whenever
//! possible.
//!
//! # Nibbles
//! A nibble (sometimes also *nybble*, *nybbl*, or *nybl*) is a 4-bit unit of data, equivalent
//! to a single-digit hexadecimal number, though individual [`Nibble`](nibble::Nibble)s will 
//! still be byte-aligned due to Rust's underlying memory guarantees.

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
