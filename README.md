# Halfling
A library of basic utilities for working with [nibbles](https://en.wikipedia.org/wiki/Nibble), representing both raw data (`halfling::nibble::Nibble`) and integral values (`halfling::integer::{I4, U4}`).

Typical usage of this crate would be to reexport one of these principal types as part of a public API, though we encourage wrapping these in newtypes while `halfling` is still pre-v1.0.0; in particular the [delegate](https://crates.io/crates/delegate) crate is useful for this purpose.

## Performance
The principal types `Nibble`, `I4`, and `U4` should operate as (almost) zero-cost wrappers over the integral-byte types `u8` and `i8`, and egregious outliers are considered bugs; we encourage you to file an issue if you find such an example!

The notable exception is bitwise operations on `I4`s, since they're backed by `i8`s which first need to be transformed into a 4-bit two's complement representation; this compromise is based on the assumption that the integral operators ought to focus on fast arithmetic operations.
