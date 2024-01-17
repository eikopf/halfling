# Halfling
A library of basic utilities for working with [nibbles](https://en.wikipedia.org/wiki/Nibble).

Typical usage of this crate would be to reexport the principal type as part of a public API, though we encourage wrapping in newtypes while `halfling` is still pre-v1.0.0; in particular the [delegate](https://crates.io/crates/delegate) crate is useful for this purpose.
