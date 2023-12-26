//! Basic utilities and structures for handling nibbles, both in raw data and integral forms.
//!
//! # Nibbles
//! A [nibble](https://en.wikipedia.org/wiki/Nibble) (sometimes also *nybble* or *nybl*)
//! is a 4-bit unit of data, equivalent in size to a single-digit hexadecimal number.
//! Historically, nibbles were used in early computers to represent small enumerations, e.g.
//! the individual digits of a base-10 number, but today they are largely API details (as
//! opposed to genuinely necessary memory-saving constructs).
//!
//! `halfling`'s [`Nibble`](nibble::Nibble) is a byte-width struct containing a single nibble,
//! which enables the 
//! [niche value optimization](https://www.noahlev.org/papers/popl22src-filling-a-niche.pdf) 
//! (a [`Nibble`](nibble::Nibble) has 4 unused bits, and hence 240 such niches are available).
//! They are byte-width due to [Rust's fundamental expectation that all types are at least 
//! byte-aligned](https://doc.rust-lang.org/reference/type-layout.html), which prevents us 
//! from constructing a single type that genuinely consumes only a nibble of memory.
//!
//! Very intentionally, [`Nibble`](nibble::Nibble) *does not* implement any of
//! [`Add`](std::ops::Add), [`Sub`](std::ops::Sub), [`Mul`](std::ops::Mul), or similar
//! operations: it is only a unit of data, and a downstream consumer of this crate should be
//! able to decide for themselves how to interpret this data and therefore how (if at all) to
//! define corresponding operations. If you want to use these operations, consider using one
//! of the integral types [`U4`](integer::U4) or [`I4`](integer::I4), which are each backed
//! by nibbles and behave (as much as possible) like the corresponding primitive integers.
//!
//! # Integers - [`I4`](integer::I4) and [`U4`](integer::U4)
//! Most commonly, nibbles are interpreted as integral values; these are included here as the
//! [`I4`](integer::I4) and [`U4`](integer::U4) types, which behave like the corresponding
//! primitive integral types. They are backed by the byte-width nibbles defined in the 
//! [`nibble`] module, and as such benefit from the niche value optimization.
//!
//! For ecosystem compatibility, these types implement the [`num_traits::Signed`] and 
//! [`num_traits::Unsigned`] traits respectively, among other [`num_traits`] traits.

// LINTS
#[warn(missing_docs)]
#[warn(rustdoc::all)]
#[warn(clippy::missing_docs_in_private_items)]
#[warn(clippy::style)]
#[warn(clippy::todo)]
#[warn(clippy::missing_errors_doc)]
#[warn(clippy::missing_panics_doc)]
#[warn(clippy::missing_safety_doc)]

// PUBLIC MODULES

pub mod error;
pub mod integer;
pub mod nibble;

// PRIVATE MODULES

mod internal;

// TODOs
//mod packed_array;
//mod packed_vec;
