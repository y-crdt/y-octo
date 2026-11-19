#!/bin/bash -eu

# The toolchain pinned by the base image may lag behind the features this
# repository uses; align with the nightly used by the repo CI. rustup
# downloads it on first use (network is available while build.sh runs).
export RUSTUP_TOOLCHAIN=nightly-2026-01-10

cd "$SRC/y-octo/y-octo-utils/fuzz"

case "${SANITIZER:-address}" in
address)
  cargo fuzz build -O --debug-assertions --sanitizer address
  ;;
coverage)
  # cargo-fuzz has no coverage sanitizer; instrument via rustflags instead.
  export RUSTFLAGS="${RUSTFLAGS:-} -Cinstrument-coverage"
  cargo fuzz build -O --sanitizer none
  ;;
*)
  echo "unsupported sanitizer: ${SANITIZER}" >&2
  exit 1
  ;;
esac

for target_src in fuzz_targets/*.rs; do
  target_name="$(basename "$target_src" .rs)"
  cp "target/x86_64-unknown-linux-gnu/release/$target_name" "$OUT/"

  # The seed corpus committed in this repo is packaged so every fuzzing run
  # (including crash reproducers added as regression seeds) starts from it.
  if [ -d "seed_corpus/$target_name" ] && [ -n "$(ls -A "seed_corpus/$target_name")" ]; then
    (cd "seed_corpus/$target_name" && zip -j -q -r "$OUT/${target_name}_seed_corpus.zip" .)
  fi
done
