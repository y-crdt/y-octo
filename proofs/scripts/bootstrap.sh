#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROOFS_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
REPO_ROOT="$(cd "$PROOFS_DIR/.." && pwd)"
TOOLS_DIR="$REPO_ROOT/.proof-tools"
LOCK_FILE="$PROOFS_DIR/toolchain-lock.json"

export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
export CI=1
export MATHLIB_NO_CACHE_ON_UPDATE=1

read_lock() {
  python3 -c "import json; print(json.load(open('$LOCK_FILE'))['$1'])"
}

RELEASE="$(read_lock aeneas_release)"
SHA256="$(read_lock linux_x86_64_archive_sha256)"
RUST_TC="$(read_lock rust_toolchain)"
LEAN_TC="$(read_lock lean_toolchain)"

mkdir -p "$TOOLS_DIR" "$PROOFS_DIR/logs"

if [ ! -x "$TOOLS_DIR/aeneas" ] || [ ! -x "$TOOLS_DIR/charon" ] || [ ! -d "$TOOLS_DIR/backends/lean" ]; then
  ARCHIVE="$TOOLS_DIR/aeneas.tar.gz"
  URL="https://github.com/AeneasVerif/aeneas/releases/download/$RELEASE/aeneas-linux-x86_64.tar.gz"
  echo "Downloading Aeneas $RELEASE..."
  curl -fL --connect-timeout 15 --max-time 540 "$URL" -o "$ARCHIVE"
  echo "$SHA256  $ARCHIVE" | sha256sum -c -
  tar xzf "$ARCHIVE" -C "$TOOLS_DIR"
  rm -f "$ARCHIVE"
fi

if ! rustup toolchain list | grep -q "^${RUST_TC}"; then
  rustup toolchain install "$RUST_TC" --profile minimal \
    --component rustc-dev --component rust-src --component llvm-tools
else
  rustup component add --toolchain "$RUST_TC" rustc-dev rust-src llvm-tools >/dev/null 2>&1 || true
fi

ELAN_VER="v4.4.0"
ELAN_SHA256="0e8250aa2be86c7af929ade68db617af9edc8b9ccf6eaf5ece228250d0d032e2"

if ! command -v elan >/dev/null 2>&1 && [ ! -x "$HOME/.elan/bin/elan" ]; then
  ELAN_ARCHIVE="$TOOLS_DIR/elan.tar.gz"
  ELAN_EXTRACT="$TOOLS_DIR/elan-extract"
  rm -rf "$ELAN_EXTRACT"
  mkdir -p "$ELAN_EXTRACT"
  echo "Installing elan $ELAN_VER..."
  curl -sSfL --connect-timeout 15 --max-time 300 -o "$ELAN_ARCHIVE" \
    "https://github.com/leanprover/elan/releases/download/${ELAN_VER}/elan-x86_64-unknown-linux-gnu.tar.gz"
  echo "${ELAN_SHA256}  ${ELAN_ARCHIVE}" | sha256sum -c -
  tar -xzf "$ELAN_ARCHIVE" -C "$ELAN_EXTRACT"
  "$ELAN_EXTRACT/elan-init" -y --default-toolchain none
  rm -rf "$ELAN_ARCHIVE" "$ELAN_EXTRACT"
fi

if ! elan toolchain list | grep -q "^${LEAN_TC}"; then
  elan toolchain install "$LEAN_TC"
fi

STAMP_FILE="$TOOLS_DIR/.bootstrap-stamp"
EXPECTED_STAMP="$(
  sha256sum \
    "$0" \
    "$LOCK_FILE" \
    "$PROOFS_DIR/lean-toolchain" \
    "$PROOFS_DIR/lakefile.lean" \
    "$PROOFS_DIR/lake-manifest.json" \
    "$REPO_ROOT/proofs-yata/lean-toolchain" \
    "$REPO_ROOT/proofs-yata/lakefile.toml" \
    "$REPO_ROOT/proofs-yata/lake-manifest.json" \
    | sha256sum | awk '{print $1}'
)"

if [ "${FORCE_LAKE_UPDATE:-0}" != "1" ] \
  && [ -f "$STAMP_FILE" ] \
  && [ "$(cat "$STAMP_FILE")" = "$EXPECTED_STAMP" ] \
  && [ -d "$TOOLS_DIR/backends/lean/.lake/packages/mathlib" ] \
  && [ -e "$PROOFS_DIR/.lake/packages" ]; then
  echo "Lean packages and mathlib cache already up to date (stamp $EXPECTED_STAMP); skipping lake update."
  exit 0
fi

(
  cd "$TOOLS_DIR/backends/lean"
  lake update
  python3 - "$TOOLS_DIR/backends/lean" <<'PY'
from pathlib import Path
import re, subprocess, sys

p = Path(sys.argv[1])
imports = sorted(set(
    m
    for f in p.glob("Aeneas*/**/*.lean")
    for m in re.findall(r"^(?:public )?(?:meta )?import (Mathlib[^\s]*)", f.read_text(), re.M)
))
if imports:
    subprocess.run(["lake", "exe", "cache", "get", *imports], cwd=p, check=True)
PY
)

mkdir -p "$PROOFS_DIR/.lake"
if [ ! -e "$PROOFS_DIR/.lake/packages" ]; then
  ln -s "../../.proof-tools/backends/lean/.lake/packages" "$PROOFS_DIR/.lake/packages"
fi

(
  cd "$PROOFS_DIR"
  lake update
)

printf '%s\n' "$EXPECTED_STAMP" > "$STAMP_FILE"
