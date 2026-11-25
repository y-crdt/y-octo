#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROOFS_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
REPO_ROOT="$(cd "$PROOFS_DIR/.." && pwd)"
TOOLS_DIR="$REPO_ROOT/.proof-tools"
LOCK_FILE="$PROOFS_DIR/toolchain-lock.json"

export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
RUST_TC="$(python3 -c "import json; print(json.load(open('$LOCK_FILE'))['rust_toolchain'])")"
export RUSTUP_TOOLCHAIN="$RUST_TC"

CHARON="$TOOLS_DIR/charon"
AENEAS="$TOOLS_DIR/aeneas"

if [ ! -x "$CHARON" ] || [ ! -x "$AENEAS" ]; then
  echo "Missing charon/aeneas in $TOOLS_DIR; run proofs/scripts/bootstrap.sh first" >&2
  exit 1
fi

CHECK_MODE=0
if [ "${1:-}" = "--check" ]; then
  CHECK_MODE=1
fi

mkdir -p "$PROOFS_DIR/logs" "$PROOFS_DIR/YoctoCore/Code"

LLBC_OUT="$REPO_ROOT/y-octo-core/y_octo_core.llbc"
rm -f "$LLBC_OUT" "$REPO_ROOT/y-octo-core/y-octo-core.llbc"

echo "[1/2] Running Charon on y-octo-core with $RUSTUP_TOOLCHAIN..."
(
  cd "$REPO_ROOT/y-octo-core"
  RUSTFLAGS="${RUSTFLAGS:-} --cfg aeneas_extract" \
    "$CHARON" cargo --preset=aeneas --sysroot default -- --lib 2>&1 | tee "$PROOFS_DIR/logs/charon.log"
)

if [ -f "$REPO_ROOT/y-octo-core/y-octo-core.llbc" ] && [ ! -f "$LLBC_OUT" ]; then
  LLBC_OUT="$REPO_ROOT/y-octo-core/y-octo-core.llbc"
fi

if [ ! -f "$LLBC_OUT" ]; then
  echo "Expected LLBC output not found in y-octo-core/" >&2
  ls -la "$REPO_ROOT/y-octo-core" >&2
  exit 1
fi

TMP_STAGE="$(mktemp -d)"
trap 'rm -rf "$TMP_STAGE"' EXIT
mkdir -p "$TMP_STAGE/YoctoCore/Code"

echo "[2/2] Running Aeneas Lean backend..."
(
  cd "$REPO_ROOT"
  "$AENEAS" -backend lean "$LLBC_OUT" \
    -dest "$TMP_STAGE" \
    -subdir YoctoCore/Code \
    -namespace YoctoCore.Code \
    -split-files \
    -abort-on-error \
    -no-progress-bar 2>&1 | tee "$PROOFS_DIR/logs/aeneas.log"
)

if [ "$CHECK_MODE" -eq 1 ]; then
  echo "Comparing fresh extraction against $PROOFS_DIR/YoctoCore/Code..."
  diff -ru "$TMP_STAGE/YoctoCore/Code" "$PROOFS_DIR/YoctoCore/Code"
  echo "Extraction tree matches committed YoctoCore/Code."
else
  rm -rf "$PROOFS_DIR/YoctoCore/Code"
  mkdir -p "$PROOFS_DIR/YoctoCore/Code"
  cp -R "$TMP_STAGE/YoctoCore/Code/." "$PROOFS_DIR/YoctoCore/Code/"
  echo "Extraction completed: $(ls -1 "$PROOFS_DIR/YoctoCore/Code")"
fi
