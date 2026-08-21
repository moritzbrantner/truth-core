#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <RESULT-ID>" >&2
  exit 2
fi

RESULT_ID="$1"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CONFIG="$ROOT/results/$RESULT_ID/comparator.json"
WORK="${TRUTH_CORE_VERIFIER_HOME:-$HOME/.cache/truth-core-verifier}"

if [[ ! -f "$CONFIG" ]]; then
  echo "unknown result or missing Comparator config: $RESULT_ID" >&2
  exit 2
fi

COMPARATOR_BIN="$WORK/rust-target/release/truth-core-comparator"
LEAN4EXPORT_BIN="$WORK/lean4export/.lake/build/bin/lean4export"
LANDRUN_BIN="$WORK/bin/landrun"
NANODA_BIN="$WORK/nanoda_lib/target/release/nanoda_bin"

for path in "$COMPARATOR_BIN" "$LEAN4EXPORT_BIN" "$LANDRUN_BIN" "$NANODA_BIN"; do
  if [[ ! -x "$path" ]]; then
    echo "missing verifier binary: $path" >&2
    echo "run scripts/bootstrap-verifier.sh first" >&2
    exit 2
  fi
done

export COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT_BIN"
export COMPARATOR_LANDRUN="$LANDRUN_BIN"
export COMPARATOR_NANODA="$NANODA_BIN"

cd "$ROOT"
echo "==> verifying $RESULT_ID"
lake env "$COMPARATOR_BIN" "$CONFIG"
