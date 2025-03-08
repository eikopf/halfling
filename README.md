# Halfling
A library of basic utilities for working with [nibbles](https://en.wikipedia.org/wiki/Nibble). This crate is entirely `#no_std` and never allocates or clones.

# Usage
The core type in `halfling` is [`Nibble`](https://docs.rs/halfling/latest/halfling/struct.Nibble.html), which is effectively a wrapper around a `u8` that guarantees it will always be strictly less than 16.

```rust
// nibbles can be constructed safely with Nibble::new
let valid_nibble = Nibble::new(10);     // returns Some(10)
let invalid_nibble = Nibble::new(16);   // returns None

// if you already know a value to be less than 16, you can use Nibble::new_unchecked
let quick_nibble = unsafe { Nibble::new_unchecked(6) };
// using Nibble::new_unchecked with a value greater than 15 is undefined behaviour
```

Because the smallest unit of memory in Rust is a byte, it isn't possible to construct a `Nibble` without consuming the redundant upper bits. However, it's possible to use some enum trickery to tell the compiler which `u8` values are valid `Nibble` values, and so the other 240 values are available as niches.

```rust
// a Nibble is a byte-width struct
assert_eq!(std::mem::size_of<Nibble>(), 1);

// because Nibble has well-defined niches, Option<Nibble> is also byte-width
assert_eq!(std::mem::size_of<Nibble>(), std::mem::size_of<Option<Nibble>>());
```

This crate also provides the `Nibbles` type, which is an iterator that wraps an `impl Iterator<Item = u8>` and yields its nibbles in order. Since the ordering of nibbles within bytes is up to interpretation (it is a kind of endianness), the `Ordering` trait is provided to explicitly control how bytes are interpreted; it is implemented by the `Le` and `Be` marker structs.

```rust
let bytes = vec![0xE2, 0x17, 0xDC];

// nibbles in little-endian order
let le = Nibbles::le(&bytes).collect::<Vec<u8>>();
// nibbles in big-endian order
let be = Nibbles::be(&bytes).collect::<Vec<u8>>();

assert!(le[0].get(), 0x2);
assert!(le[1].get(), 0xE);
assert!(le[2].get(), 0x7);
assert!(le[3].get(), 0x1);
assert!(le[4].get(), 0xC);
assert!(le[5].get(), 0xD);

assert!(be[0].get(), 0xE);
assert!(be[1].get(), 0x2);
assert!(be[2].get(), 0x1);
assert!(be[3].get(), 0x7);
assert!(be[4].get(), 0xD);
assert!(be[5].get(), 0xC);
```
