# Y-Octo

[![test](https://github.com/toeverything/y-octo/actions/workflows/y-octo.yml/badge.svg)](https://github.com/toeverything/y-octo/actions/workflows/y-octo.yml)
[![docs]](https://docs.rs/y-octo/latest/y_octo)
[![crates]](https://crates.io/crates/y-octo)
[![codecov]](https://codecov.io/gh/toeverything/y-octo)

Y-Octo is a high-performance CRDT implementation compatible with [yjs].

## Introduction

Y-Octo is a tiny, ultra-fast CRDT collaboration library built for all major platforms. Developers can use Y-Octo as the [Single source of truth](https://en.wikipedia.org/wiki/Single_source_of_truth) for their application state, naturally turning the application into a [local-first](https://www.inkandswitch.com/local-first/) collaborative app.

Y-Octo also has interoperability and binary compatibility with [yjs]. Developers can use [yjs] to develop local-first web applications and collaborate with Y-Octo in native apps alongside web apps.

## Editor integration

- Group one editor action in `Doc::transact_mut` and edit through the transaction's text, array or map view. Returning an error preserves changes already made. Replace polling with `Doc::subscribe` and keep the returned subscription alive. Callbacks receive commits in order after the document unlocks.
- Store a selection as relative positions. Text offsets count UTF-16 code units. A negative association anchors to the preceding content. Resolve after synchronization and handle a missing or deleted target. Enable redo following for a local selection that should track recreated content.
- Use `Doc::apply_local_update` for the bytes from one trusted renderer transaction with its own client ID. Apply peer updates and accumulated sync diffs as remote updates so peer deletions stay out of local undo. On `MissingDependencies`, synchronize the missing clocks before retrying.
- Share one scoped `UndoManager` per document. Register the renderer origin and reuse clones of that instance. Call `stop_capturing` between gestures. Undo history and origins are local to the document.
- With default features disabled, initialize each replica with `DocOptions::from_identity`. Use a distinct JavaScript-safe client ID and supply a fresh one if `client_required()` becomes true.

Run the API examples with `cargo test -p y-octo --doc`. The Rust crate exchanges Yjs Update V1 with other clients. Applications that used the removed Node binding need an adapter.

### Compatibility limits

The default decoder accepts `Any` nesting up to 128 levels. For trusted inputs, set the limit with `Update::decode_v1_with_max_any_depth`, `ReadLimits::max_any_depth` or `Any::read_with_max_depth`. The maximum is 1,024.

`Awareness` starts without a local state. A remote update for the local client ID can advance the clock used for the next broadcast, but only the local client can set its state.

## Who are using

<a href="https://affine.pro"><img src="./assets/affine.svg" /></a>

[AFFiNE](https://affine.pro) is using y-octo in production. There are [Electron](https://affine.pro/download) app and [Node.js server](https://github.com/toeverything/AFFiNE/tree/canary/packages/backend/native) using y-octo in production.

<a href="https://www.mysc.app/"><img src="https://www.mysc.app/images/logo_blk.webp" width="120px" /></a>

[Mysc](https://www.mysc.app/) is using y-octo in the Rust server, and the iOS/Android client via the Swift/Kotlin bindings (Official bindings coming soon).

## Performance

| Tasks | automerge v0.12.0 (2026-09-16) | loro v1.19.1 (2026-11-24) | diamond-types v1.0.0 (2022-08-25) | y-octo v0.4.1 (`b6ec39b`) | yrs v0.28.2 (2026-11-19) | crdt(pion) v0.2.0 (`f66e02f`) |
| :---- | :---- | :---- | :---- | :---- | :---- | :---- |
| automerge - apply | 2087.10 ± 1.91 ms | 48.92 ± 0.21 ms | 9.57 ± 0.04 ms | 98.39 ± 0.16 ms | 2438.34 ± 24.32 ms | 556.21 ± 2.54 ms |
| automerge - decode time | 201.84 ± 1.86 ms | 90.64 ± 0.46 us | 1.53 ± 0.01 ms | 2.64 ± 0.00 ms | 2.42 ± 0.02 ms | 3.44 ± 0.04 ms |
| automerge - encode time | 146.25 ± 0.44 us | 45.16 ± 0.13 us | 761.55 ± 4.69 us | 370.21 ± 0.69 us | 402.73 ± 3.38 us | 6.79 ± 0.39 ms |
| concurrent list inserts | 113.36 ± 0.27 ms | 75.79 ± 1.56 ms | 35.43 ± 0.38 ms | 5.96 ± 0.02 ms | 7.57 ± 0.03 ms | 7.97 ± 0.10 ms |
| list_random_insert_1k | 331.43 ± 0.63 ms | 5.22 ± 0.03 ms | 2.72 ± 0.06 ms | 1.37 ± 0.00 ms | 3.38 ± 0.06 ms | 1.78 ± 0.01 ms |
| parallel applying automerge edits | 8413.91 ± 29.70 ms | 200.95 ± 1.36 ms | 88.47 ± 0.38 ms | 315.97 ± 0.51 ms | 6044.18 ± 83.54 ms | 1533.16 ± 27.67 ms |
| text - append 50k | 144.56 ± 0.23 ms | 6.16 ± 0.02 ms | 1.19 ± 0.01 ms | 5.83 ± 0.05 ms | 13.57 ± 0.07 ms | 7.48 ± 0.11 ms |
| text - backspace 50k | 97.65 ± 0.18 ms | 1006.59 ± 6.24 ms | 2.86 ± 0.01 ms | 26.44 ± 0.02 ms | 1774.49 ± 5.07 ms | 1020.77 ± 4.73 ms |
| text - random edits 20k | 250.50 ± 0.35 ms | 6.13 ± 0.08 ms | 1.63 ± 0.01 ms | 14.54 ± 0.11 ms | 421.82 ± 2.64 ms | 30.05 ± 0.20 ms |
| text - tombstone 50k | 320.08 ± 0.35 ms | 152.87 ± 0.87 ms | 3.33 ± 0.01 ms | 31.39 ± 0.08 ms | 2120.27 ± 30.28 ms | 1768.38 ± 132.89 ms |

Measured on Apple M5 Max (macOS arm64) with rustc 1.96.0, pionc 0.1.0 (ABI pionc-v0.22), and `crdt-bench-native` revision `29c7c67`. Values show mean elapsed time ± standard error across 10 samples. The Rust adapters use Criterion. The Pion adapter uses a monotonic clock. y-octo and Pion use Update V1, with `large_refs` enabled for y-octo. Yrs uses Update V2.

The parallel workload applies the full Automerge trace to two replicas in random batches of 1–1000 local edits, synchronizes after each pair of batches, and verifies replica convergence. The four `text - *` workloads run deterministic pure-ASCII text editing patterns (sequential 50k appends, 50k single-char tail backspaces, 20k mixed cursor/random edits, and 50k half-deleted tombstone field + 10k random inserts) verified for identical final text across all six implementations.

Ref: https://github.com/darkskygit/crdt-bench-native

## Features

- ✅ Supported by Yjs and compatible with y-octo
- 🚧 Supported by Yjs and in development for y-octo
- ➕ Exclusive to y-octo

- **Collaborative text**
  - ✅ Rich-text deltas, formatting attributes, and UTF-16 offsets
  - ✅ Embedded JavaScript values (`Any`)
  - 🚧 Inserting shared types as text embeds
- **Shared collections and XML**
  - ✅ Arrays and maps containing plain values or nested shared types
  - ✅ XML fragments, elements, text nodes, and hooks
- **Documents and transactions**
  - ✅ Group edits into a transaction and observe changes to a document or subtree
  - ✅ Track subdocuments added or removed by a transaction
  - ➕ Share document and type handles across Rust threads
- **Editor tools**
  - ✅ Scoped undo and redo with tracked origins and independent undo stacks
  - ✅ Relative positions for cursors and selections across peer edits
  - ➕ Manage nested transaction frames, type paths, and undo stacks by ID with `DocSession`
- **Updates and protocols**
  - ✅ Encode and apply Update V1, exchange state vectors, and diff or merge encoded updates
  - ✅ Exchange sync and awareness messages with `y-protocols` peers
  - 🚧 Update V2 encoding and decoding
  - ➕ Validate V1 update bytes before applying them with `validate_update_v1`
  - ➕ Query a full V1 update through the read-only `ReadDoc` view
  - ➕ Compute a V1 delta back to an ancestor snapshot with `revert_update_v1`
- **WebAssembly**
  - ➕ Use `DocSession` from JavaScript through a Wasm module with no host imports
  - ➕ Insert or remove text and read its UTF-16 length through direct Wasm calls
- **Rust core and verification**
  - ➕ The document engine and its dependency-free, `no_std` core forbid unsafe Rust
  - ➕ Lean 4 proofs cover client clock lookup, deletion ranges, and conflict-scan decisions used by the document engine
  - ➕ Differential tests replay the same edits in Rust and an executable Lean model of YATA

## Testing & Linting

Put everything to the test! We've established various test suites, but we're continually striving to enhance our coverage：

- Rust Tests
  - Unit tests
  - [Loom](https://docs.rs/loom/latest/loom/) multi-threading tests
  - [Miri](https://github.com/rust-lang/miri) undefined behavior tests
  - [Address Sanitizer](https://doc.rust-lang.org/beta/unstable-book/compiler-flags/sanitizer.html) memory error detections
  - [Fuzzing](https://github.com/rust-fuzz/cargo-fuzz) fuzzing tests
- [Yjs interoperability tests](y-octo/tests/oracle/README.md) and a WebAssembly smoke test run by Node.js
- Smoke Tests
- Formatting and Clippy

## Related projects

- [OctoBase]: The open-source embedded database based on Y-Octo.
- [yjs]: Shared data types for building collaborative software in web.

## Maintainers

- [DarkSky](https://github.com/darkskygit)
- [liuyi](https://github.com/forehalo)
- [LongYinan](https://github.com/Brooooooklyn)

## License

Y-Octo are [MIT licensed].

[codecov]: https://codecov.io/gh/toeverything/y-octo/graph/badge.svg?token=9AQY5Q1BYH
[crates]: https://img.shields.io/crates/v/y-octo.svg
[docs]: https://img.shields.io/docsrs/y-octo.svg
[test]: https://github.com/toeverything/y-octo/actions/workflows/y-octo.yml/badge.svg
[yjs]: https://github.com/yjs/yjs
[Address Sanitizer]: https://github.com/toeverything/y-octo/actions/workflows/y-octo-asan.yml/badge.svg
[Memory Leak Detect]: https://github.com/toeverything/y-octo/actions/workflows/y-octo-memory-test.yml/badge.svg
[OctoBase]: https://github.com/toeverything/octobase
[BlockSuite]: https://github.com/toeverything/blocksuite
[AFFiNE]: https://github.com/toeverything/affine
[MIT licensed]: ./LICENSE
