# y-octo-core

The pure, `unsafe`-free CRDT core of [y-octo](https://crates.io/crates/y-octo).

It is `no_std` (with `alloc`) and has no dependencies. The code is extracted to Lean 4 with Charon and Aeneas, and the proofs in [`proofs/`](https://github.com/toeverything/y-octo/tree/main/proofs) refine it against the YATA model in [`proofs-yata/`](https://github.com/toeverything/y-octo/tree/main/proofs-yata).

Most users want [`y-octo`](https://crates.io/crates/y-octo), which builds the Yjs-compatible document on top of this crate.

## License

MIT
