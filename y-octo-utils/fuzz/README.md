# y-octo fuzzing

Fuzz targets for `y-octo`, driven by [cargo-fuzz](https://github.com/rust-fuzz/cargo-fuzz) (libFuzzer).
Continuous fuzzing runs through [ClusterFuzzLite](https://google.github.io/clusterfuzzlite/) in GitHub Actions
(see `.github/workflows/cflite_*.yml`); no external infrastructure is required — corpora, crashes and coverage
reports are stored as workflow artifacts.

## Targets

| Target               | What it covers                                                             |
| -------------------- | -------------------------------------------------------------------------- |
| `decode_doc_update`  | decoding arbitrary (malformed) bytes as a yjs update into `Doc`            |
| `apply_update`       | differential: yrs-built docs must decode/re-encode identically in y-octo, and y-octo re-encodings must stay decodable by yrs |
| `codec_doc_any`      | `Any` decoding from arbitrary bytes, then re-encode/decode roundtrip       |
| `codec_doc_any_struct` | structured `Any` (object/array) encode/decode roundtrip                  |
| `sync_message`       | sync protocol message decoding + re-encode roundtrip                       |
| `ins_del_text`       | structured text insert/remove sequences keep length invariants             |
| `decode_bytes`       | varint/buffer/string readers never panic on arbitrary bytes                |
| `i32`/`u64` `_encode`/`_decode` | varint codecs match lib0 byte-for-byte                          |

## Running locally

```bash
cargo +nightly fuzz run <target>          # fuzz one target
cargo +nightly fuzz run <target> -- -runs=1000   # bounded smoke run
```

## Seed corpus and crash regression loop

Two corpus locations exist on purpose:

- `corpus/<target>/` — the fuzzer's working corpus. **Ignored by git**, free to
  grow during local runs; the accumulated CI corpus lives in ClusterFuzzLite
  artifacts and is pruned daily by the `cflite_cron` workflow.
- `seed_corpus/<target>/` — **committed to the repo**. Packaged into every
  ClusterFuzzLite build as `<target>_seed_corpus.zip`, so every run replays it
  first. This makes it both a seed corpus and the regression mechanism: any
  input committed here is re-checked by every CI fuzzing run.

When a crash is found (locally or via a CI artifact):

1. Reproduce: `cargo +nightly fuzz run <target> <crash-file>`
2. Minimize: `cargo +nightly fuzz tmin <target> <crash-file>`
3. Fix the bug, then commit the minimized input to `seed_corpus/<target>/` together with the fix.

Keep the committed seed corpus small: only handcrafted seeds and minimized
crash reproducers belong in `seed_corpus/`; never commit the fuzzer's working
corpus. If you want to shrink a bloated local corpus, use
`cargo +nightly fuzz cmin <target>`.
