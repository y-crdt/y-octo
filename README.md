# Y-Octo

[![docs]](https://docs.rs/crate/y-octo)
[![crates]](https://crates.io/crates/y-octo)

Y-Octo is a high-performance CRDT implementation compatible with [yjs].

### Introduction

Y-Octo is a tiny, ultra-fast CRDT collaboration library built for all major platforms. Developers can use Y-Octo as the [Single source of truth](https://en.wikipedia.org/wiki/Single_source_of_truth) for their application state, naturally turning the application into a [local-first](https://www.inkandswitch.com/local-first/) collaborative app.

Y-Octo also has interoperability and binary compatibility with [yjs]. Developers can use [yjs] to develop local-first web applications and collaborate with Y-Octo in native apps alongside web apps.

### Code Robustness

[![Lint & Test & Fuzzing]](https://github.com/toeverything/y-octo/actions/workflows/y-octo.yml)
[![Address Sanitizer]](https://github.com/toeverything/y-octo/actions/workflows/asan.yml)
[![Memory Leak Detect]](https://github.com/toeverything/y-octo/actions/workflows/memory-test.yml)
[![codecov]](https://codecov.io/gh/toeverything/y-octo)

### Features

- ✅ Collaborative Text
  - ✅Read and write styled Unicode compatible data.
  - 🚧 Add, modify and delete text styles.
  - 🚧 Embedded JS data types and collaborative types.
  - ✅ Collaborative types of thread-safe.
- Collaborative Array
  - ✅ Add, modify, and delete basic JS data types.
  - ✅ Recursively add, modify, and delete collaborative types.
  - ✅ Collaborative types of thread-safe.
  - 🚧 Recursive event subscription
- Collaborative Map
  - ✅ Add, modify, and delete basic JS data types.
  - ✅ Recursively add, modify, and delete collaborative types.
  - ✅ Collaborative types of thread-safe.
  - 🚧 Recursive event subscription
- 🚧 Collaborative Xml (Fragment / Element)
- ✅ Collaborative Doc Container
  - ✅ YATA CRDT state apply/diff compatible with [yjs]
  - ✅ State sync of thread-safe.
  - ✅ Store all collaborative types and JS data types
  - ✅ Update event subscription.
  - 🚧 Sub Document.
- ✅ Yjs binary encoding
  - ✅ Awareness encoding.
  - ✅ Primitive type encoding.
  - ✅ Sync Protocol encoding.
  - ✅ Yjs update v1 encoding.
  - 🚧 Yjs update v2 encoding.

### Testing & Linting

Put everything to the test! We've established various test suites, but we're continually striving to enhance our coverage：

- Rust Tests
- Node Tests
- Smoke Tests
- eslint, clippy

### Related projects

- [OctoBase]: The open-source embedded database based on Y-Octo.
- [yjs]: Shared data types for building collaborative software in web.

[codecov]: https://codecov.io/gh/toeverything/y-octo/graph/badge.svg?token=9AQY5Q1BYH
[crates]: https://img.shields.io/crates/v/y-octo.svg
[docs]: https://img.shields.io/crates/v/y-octo.svg
[yjs]: https://github.com/yjs/yjs
[Lint & Test & Fuzzing]: https://github.com/toeverything/y-octo/actions/workflows/y-octo.yml/badge.svg
[Address Sanitizer]: https://github.com/toeverything/y-octo/actions/workflows/y-octo-asan.yml/badge.svg
[Memory Leak Detect]: https://github.com/toeverything/y-octo/actions/workflows/y-octo-memory-test.yml/badge.svg
[OctoBase]: https://github.com/toeverything/octobase
[BlockSuite]: https://github.com/toeverything/blocksuite
[AFFiNE]: https://github.com/toeverything/affine
