#!/usr/bin/env bash
set -euo pipefail

# Run Miri checks for `y-octo` with adaptive parallelism and process reuse for
# `--lib` unit tests to avoid paying Miri cold-start overhead on every test.
#
# Environment variables:
#   TOOLCHAIN   Rustup nightly toolchain (default: nightly-2026-01-10)
#   MIRI_JOBS   Parallel worker count (default: min(4, nproc))

TOOLCHAIN="${TOOLCHAIN:-nightly-2026-01-10}"

if [ -z "${MIRI_JOBS:-}" ]; then
  CORES="$(nproc 2>/dev/null || getconf _NPROCESSORS_ONLN 2>/dev/null || echo 2)"
  JOBS=$((CORES > 4 ? 4 : CORES))
else
  JOBS="$MIRI_JOBS"
fi
if [ "$JOBS" -lt 1 ]; then
  JOBS=1
fi

echo "==> Miri: toolchain=${TOOLCHAIN}, jobs=${JOBS}"

# Stage 1: compile `--lib` once, list all unit tests, and run them across
# $JOBS long-lived Miri processes (round-robin) so each shard pays Miri's
# cold-start cost only once and reuses `OnceLock` fixture caches.
echo "==> Stage 1: compiling y-octo --lib for Miri"
cargo "+${TOOLCHAIN}" miri test -p y-octo --lib --no-run

TMP_DIR="$(mktemp -d)"
trap 'rm -rf "$TMP_DIR"' EXIT

LIST_FILE="$TMP_DIR/tests.txt"
RAW_LIST="$TMP_DIR/raw-list.txt"

if ! cargo "+${TOOLCHAIN}" miri test -p y-octo --lib -- --list --format=terse >"$RAW_LIST" 2>"$TMP_DIR/list.stderr"; then
  cargo "+${TOOLCHAIN}" miri test -p y-octo --lib -- --list >"$RAW_LIST"
fi

sed -n 's/: test$//p' "$RAW_LIST" | sort >"$LIST_FILE"
TOTAL_LISTED="$(wc -l <"$LIST_FILE" | tr -d '[:space:]')"

if [ "$TOTAL_LISTED" -eq 0 ]; then
  echo "error: failed to discover any y-octo --lib tests for Miri" >&2
  cat "$RAW_LIST" >&2
  exit 1
fi

SHARD_COUNT="$JOBS"
if [ "$SHARD_COUNT" -gt "$TOTAL_LISTED" ]; then
  SHARD_COUNT="$TOTAL_LISTED"
fi

echo "==> Stage 1: running ${TOTAL_LISTED} --lib tests across ${SHARD_COUNT} Miri processes"

# Distribute tests round-robin so heavy tests in the same module spread evenly.
for i in $(seq 0 $((SHARD_COUNT - 1))); do
  : >"$TMP_DIR/shard-${i}.txt"
done

idx=0
while IFS= read -r test_name; do
  shard=$((idx % SHARD_COUNT))
  printf '%s\n' "$test_name" >>"$TMP_DIR/shard-${shard}.txt"
  idx=$((idx + 1))
done <"$LIST_FILE"

pids=()
for i in $(seq 0 $((SHARD_COUNT - 1))); do
  shard_file="$TMP_DIR/shard-${i}.txt"
  log_file="$TMP_DIR/shard-${i}.log"
  tests=()
  while IFS= read -r line; do
    [ -n "$line" ] && tests+=("$line")
  done <"$shard_file"
  (
    cargo "+${TOOLCHAIN}" miri test -p y-octo --lib -- --exact --test-threads=1 "${tests[@]}"
  ) >"$log_file" 2>&1 &
  pids+=("$!")
done

failed_shards=0
for i in $(seq 0 $((SHARD_COUNT - 1))); do
  pid="${pids[$i]}"
  log_file="$TMP_DIR/shard-${i}.log"
  if wait "$pid"; then
    summary="$(grep -E '^test result:' "$log_file" | tail -n 1 || true)"
    echo "  shard ${i}: ${summary:-ok}"
  else
    echo "  shard ${i}: FAILED" >&2
    cat "$log_file" >&2
    failed_shards=$((failed_shards + 1))
  fi
done

if [ "$failed_shards" -ne 0 ]; then
  echo "error: ${failed_shards} Miri --lib shard(s) failed" >&2
  exit 1
fi

# Strictly verify every listed test was accounted for (passed + ignored == listed, 0 failed).
TOTAL_PASSED=0
TOTAL_FAILED=0
TOTAL_IGNORED=0
for i in $(seq 0 $((SHARD_COUNT - 1))); do
  log_file="$TMP_DIR/shard-${i}.log"
  summary="$(grep -E '^test result:' "$log_file" | tail -n 1 || true)"
  if [ -z "$summary" ]; then
    echo "error: missing 'test result:' line in shard ${i}" >&2
    cat "$log_file" >&2
    exit 1
  fi
  passed="$(printf '%s\n' "$summary" | sed -E 's/.* ([0-9]+) passed;.*/\1/')"
  failed="$(printf '%s\n' "$summary" | sed -E 's/.*; ([0-9]+) failed;.*/\1/')"
  ignored="$(printf '%s\n' "$summary" | sed -E 's/.*; ([0-9]+) ignored;.*/\1/')"
  TOTAL_PASSED=$((TOTAL_PASSED + passed))
  TOTAL_FAILED=$((TOTAL_FAILED + failed))
  TOTAL_IGNORED=$((TOTAL_IGNORED + ignored))
done

ACCOUNTED=$((TOTAL_PASSED + TOTAL_IGNORED))
echo "==> Stage 1 complete: ${TOTAL_PASSED} passed, ${TOTAL_FAILED} failed, ${TOTAL_IGNORED} ignored (listed ${TOTAL_LISTED})"

if [ "$TOTAL_FAILED" -ne 0 ] || [ "$ACCOUNTED" -ne "$TOTAL_LISTED" ] || [ "$TOTAL_PASSED" -eq 0 ]; then
  echo "error: Miri --lib test count mismatch (accounted=${ACCOUNTED}, listed=${TOTAL_LISTED}, passed=${TOTAL_PASSED}, failed=${TOTAL_FAILED})" >&2
  exit 1
fi

# Stage 2: run integration tests ONLY (`--test '*'`, excluding `--lib` which
# already ran in Stage 1) via cargo-nextest (fallback to cargo miri test if
# nextest is absent).
if cargo nextest --version >/dev/null 2>&1; then
  echo "==> Stage 2: running y-octo integration tests (--test '*') with Miri nextest (-j ${JOBS})"
  cargo "+${TOOLCHAIN}" miri nextest run -p y-octo --test '*' -j "$JOBS"
else
  echo "==> Stage 2: running y-octo integration tests (--test '*') with cargo miri test"
  cargo "+${TOOLCHAIN}" miri test -p y-octo --test '*'
fi
