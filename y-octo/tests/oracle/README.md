# Yjs interoperability tests

Run from the project root with Node.js 22 or later. The pinned Yjs versions
generate the expected states and Update V1 bytes. Rust replays the checked-in
fixtures offline. Where versions differ, the reference is Yjs 13.6.33.

```sh
npm ci --prefix y-octo/tests/oracle --ignore-scripts
npm run check --prefix y-octo/tests/oracle
cargo test -p y-octo --features large_refs --test yjs_live_oracle --test yjs_concurrent_oracle
```

After an intentional fixture change, run `npm run generate --prefix y-octo/tests/oracle`.
Inspect a single record with `node y-octo/tests/oracle/unpack.mjs live.jsonl.gz live-map-1`.
