#!/usr/bin/env bash
# Every module under TruthCore/ except result challenges (Challenge.lean) is
# imported by exactly one generated per-area aggregator TruthCore/Imports/<Area>.lean,
# and TruthCore.lean imports only the aggregators (#416). See scripts/root_imports.py.
#
#   scripts/root-imports.sh          check (CI); exits 1 and prints a diff if stale
#   scripts/root-imports.sh --write  regenerate the aggregators and TruthCore.lean
set -euo pipefail
exec python3 "$(dirname "$0")/root_imports.py" "$@"
