#!/usr/bin/env bash
# TruthCore.lean imports every module under TruthCore/ except result
# challenges (Challenge.lean, which state `sorry` goals), one per line, sorted
# bytewise. Sorted order lets concurrent PRs add imports at different lines
# instead of all appending at the end.
#
#   scripts/root-imports.sh          check (CI); exits 1 and prints a diff if stale
#   scripts/root-imports.sh --write  regenerate TruthCore.lean
set -euo pipefail
cd "$(dirname "$0")/.."

expected() {
  find TruthCore -name '*.lean' ! -name Challenge.lean \
    | sed 's/\.lean$//; s#/#.#g; s/^/import /' \
    | LC_ALL=C sort
}

if [[ "${1:-}" == "--write" ]]; then
  expected > TruthCore.lean
elif ! diff -u TruthCore.lean <(expected); then
  echo "TruthCore.lean is stale: run scripts/root-imports.sh --write" >&2
  exit 1
fi
