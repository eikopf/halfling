# Halfling
This library contains basic utilities for working with [nibbles](https://en.wikipedia.org/wiki/Nibble), largely just to offload some of the API details of dealing with them as raw bytes.

In particular, special care is taken to reduce the memory usage of nibbles, applying niche value optimizations and compacting some collections whenever possible.
