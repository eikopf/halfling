# Halfling
A library of basic utilities for working with [nibbles](https://en.wikipedia.org/wiki/Nibble).

# Usage
The core type in `halfling` is [`Nibble`](https://docs.rs/halfling/latest/halfling/struct.Nibble.html), which is effectively a wrapper around a `u8` that guarantees it will always be strictly less than 16.

```rust
// nibbles can be constructed safely with Nibble::new
let valid_nibble = Nibble::new(10);     // returns Some(10)
let invalid_nibble = Nibble::new(16);   // returns None

// if you already know a value to be less than 16, you can use Nibble::new_unchecked
let quick_nibble = unsafe { Nibble::new_unchecked(6) };
// using Nibble::new_unchecked with a value greater than 16 is undefined behaviour
```

Because the smallest unit of memory in Rust is a byte, it isn't possible to construct `Nibble` without the redundant upper bits. However, it's possible to use some enum trickery to tell the compiler which `u8` values are valid `Nibble` values, and so the other 240 values are available as niches.

```rust
// a Nibble is a byte-width struct
assert_eq!(std::mem::size_of<Nibble>(), 1);

// because Nibble has well-defined niches, Option<Nibble> is also byte-width
assert_eq!(std::mem::size_of<Nibble>(), std::mem::size_of<Option<Nibble>>());

// currently, it seems like rustc can't apply the same optimisation to non-unit enum variants
assert_eq!(std::mem::size_of<Result<Nibble, Nibble>>(), 2)
```
