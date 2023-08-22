# Y-Octo

[![docs]](https://docs.rs/crate/y-octo)
[![crates]](https://crates.io/crates/y-octo)

Y-Octo is a high-performance CRDT implementation compatible with [yjs].

## Introduction

Y-Octo is a tiny, ultra-fast CRDT collaboration library built for all major platforms. Developers can use Y-Octo as the [Single source of truth](https://en.wikipedia.org/wiki/Single_source_of_truth) for their application state, naturally turning the application into a [local-first](https://www.inkandswitch.com/local-first/) collaborative app.

Y-Octo also has interoperability and binary compatibility with [yjs]. Developers can use [yjs] to develop local-first web applications and collaborate with Y-Octo in native apps alongside web apps.

### Code Robustness

[![Lint & Test & Fuzzing]](https://github.com/toeverything/y-octo/actions/workflows/y-octo.yml)
[![Address Sanitizer]](https://github.com/toeverything/y-octo/actions/workflows/asan.yml)
[![Memory Leak Detect]](https://github.com/toeverything/y-octo/actions/workflows/memory-test.yml)
[![codecov]](https://codecov.io/gh/toeverything/y-octo)

###

## Features

- [x] Collaborative Text
  - [x] Read and write styled Unicode compatible data.
  - [ ] Add, modify and delete text styles.
  - [ ] Embedded JS data types and collaborative types.
  - [x] Collaborative types of thread-safe.
- [x] Collaborative Array and Map
  - [x] Add, modify, and delete basic JS data types.
  - [x] Recursively add, modify, and delete collaborative Rich-Text, Map, and Array data types.
  - [x] Collaborative types of thread-safe.
  - [ ] Recursive event subscription
- [ ] Xml series yjs types
- [x] Collaborative Doc Container
  - [x] YATA CRDT state apply/diff compatible with [yjs]
  - [x] State sync of thread-safe.
  - [x] Store all collaborative types and JS data types
  - [x] Update event subscription.
  - [x] Yjs primitive type encoding.
  - [x] Yjs v1 encoding.
  - [ ] Yjs v2 encoding.

[codecov]: https://codecov.io/gh/toeverything/y-octo/graph/badge.svg?token=9AQY5Q1BYH
[crates]: https://img.shields.io/crates/v/y-octo.svg
[docs]: https://img.shields.io/crates/v/y-octo.svg
[yjs]: https://github.com/yjs/yjs
[Lint & Test & Fuzzing]: https://github.com/toeverything/y-octo/actions/workflows/y-octo.yml/badge.svg
[Address Sanitizer]: https://github.com/toeverything/y-octo/actions/workflows/y-octo-asan.yml/badge.svg
[Memory Leak Detect]: https://github.com/toeverything/y-octo/actions/workflows/y-octo-memory-test.yml/badge.svg
