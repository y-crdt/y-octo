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

| Tasks | automerge v0.12.0 (2026-09-16) | loro v1.18.0 (2026-11-16) | diamond-types v1.0.0 (2022-08-25) | y-octo v0.4.0 | yrs v0.28.2 (2026-11-19) |
| :---- | :---- | :---- | :---- | :---- | :---- |
| automerge - apply | 2136.55 ± 8.88 ms | 49.37 ± 0.43 ms | 9.57 ± 0.07 ms | 165.96 ± 0.38 ms | 2358.02 ± 20.35 ms |
| automerge - decode time | 210.56 ± 2.51 ms | 106.23 ± 0.21 us | 1.46 ± 0.01 ms | 3.79 ± 0.01 ms | 2.45 ± 0.02 ms |
| automerge - encode time | 155.90 ± 1.51 us | 174.01 ± 1.31 us | 717.02 ± 3.28 us | 568.37 ± 3.92 us | 426.80 ± 6.78 us |
| concurrent list inserts | 77.62 ± 0.36 ms | 102.69 ± 1.65 ms | 35.17 ± 0.25 ms | 7.37 ± 0.03 ms | 7.76 ± 0.07 ms |
| list_random_insert_1k | 337.38 ± 4.14 ms | 8.20 ± 0.12 ms | 2.56 ± 0.00 ms | 1.81 ± 0.00 ms | 3.19 ± 0.02 ms |
| parallel applying automerge edits | 8351.01 ± 15.00 ms | 182.84 ± 1.47 ms | 91.69 ± 0.79 ms | 405.87 ± 1.47 ms | 6264.56 ± 126.42 ms |

Measured on Apple M5 Max with rustc 1.96.0 and crdt-bench-native revision `0452093`. Each value is the Criterion mean ± standard error across 10 samples. The y-octo adapter uses Update V1 with `large_refs`; the Yrs adapter uses Update V2.

The parallel workload applies the full Automerge trace to two replicas in random batches of 1–1000 local edits, synchronizes after each pair of batches, and verifies replica convergence.

Ref: https://github.com/darkskygit/crdt-bench-native

## Features

- ✅: Supported by yjs; supported and compatible with y-octo
- 🚧: Supported by yjs; in development for y-octo
- ➕: Exclusive to y-octo

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
  - ➕ Validate a complete V1 update with `validate_update_v1`
  - ➕ Query a full V1 update through the read-only `ReadDoc` view
  - ➕ Compute a V1 delta back to an ancestor snapshot with `revert_update_v1`
- **WebAssembly**
  - ➕ Use `DocSession` from JavaScript through a Wasm module with no host imports
- **Code quality**
  - ➕ A completely unsafe-free, thread-safe implementation of Yjs

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
