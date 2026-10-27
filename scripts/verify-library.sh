#!/usr/bin/env bash
set -euo pipefail

# Check the built TruthCore library with NanoDa.
#
#   scripts/verify-library.sh          scoped: every TruthCore declaration together with every
#                                      declaration it depends on (Mathlib, Lean core), and nothing else
#   scripts/verify-library.sh --full   everything TruthCore imports, including Mathlib declarations
#                                      that no TruthCore declaration uses
#   scripts/verify-library.sh --modules FILE
#                                      scoped, restricted to the declarations of the TruthCore modules
#                                      listed in FILE, together with everything they depend on
#
# The scoped check trusts nothing it does not check: lean4export exports the full dependency
# closure of the listed constants. The full check adds only unused library declarations; CI runs
# it once per Mathlib/toolchain/NanoDa pin and set of external imports (docs/axiom-policy.md).
# CI passes --modules only on a pull request, with the modules whose build output the change can
# affect (scripts/affected_results.py nanoda-modules); main and nightly runs check every declaration.

usage() {
  echo "usage: $0 [--full | --modules FILE]" >&2
  exit 2
}

MODE=scoped
MODULES_FILE=""
case "${1:-}" in
  "") [[ $# -eq 0 ]] || usage ;;
  --full) [[ $# -eq 1 ]] || usage; MODE=full ;;
  --modules) [[ $# -eq 2 ]] || usage; MODULES_FILE="$2" ;;
  *) usage ;;
esac
if [[ -n "$MODULES_FILE" ]]; then
  [[ -f "$MODULES_FILE" ]] || { echo "missing modules file: $MODULES_FILE" >&2; exit 2; }
  MODULES_FILE="$(cd "$(dirname "$MODULES_FILE")" && pwd)/$(basename "$MODULES_FILE")"
fi

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORK="${TRUTH_CORE_VERIFIER_HOME:-$HOME/.cache/truth-core-verifier}"
LEAN4EXPORT_BIN="$WORK/lean4export/.lake/build/bin/lean4export"
NANODA_BIN="$WORK/nanoda_lib/target/release/nanoda_bin"

for path in "$LEAN4EXPORT_BIN" "$NANODA_BIN"; do
  if [[ ! -x "$path" ]]; then
    echo "missing verifier binary: $path" >&2
    echo "run scripts/bootstrap-verifier.sh first" >&2
    exit 2
  fi
done

# lean4export reads .olean files and must be built for the pinned Lean version.
if [[ -f "$WORK/lean4export/lean-toolchain" ]] &&
  [[ "$(tr -d '[:space:]' < "$WORK/lean4export/lean-toolchain")" != \
    "$(tr -d '[:space:]' < "$ROOT/lean-toolchain")" ]]; then
  echo "lean4export in $WORK was built for $(cat "$WORK/lean4export/lean-toolchain")," >&2
  echo "but lean-toolchain pins $(cat "$ROOT/lean-toolchain"); re-run scripts/bootstrap-verifier.sh" >&2
  exit 2
fi

TEMP="$(mktemp -d)"
trap 'rm -rf "$TEMP"' EXIT
EXPORT="$TEMP/truth-core.ndjson"
CONFIG="$TEMP/nanoda.json"

cd "$ROOT"
if [[ "$MODE" == full ]]; then
  echo "==> exporting TruthCore and everything it imports"
  lake env "$LEAN4EXPORT_BIN" TruthCore > "$EXPORT" 2> "$TEMP/export.err"
else
  if [[ -n "$MODULES_FILE" ]]; then
    MODE="scoped to $(grep -c . "$MODULES_FILE" || true) listed modules"
    echo "==> listing the declarations of the TruthCore modules in $MODULES_FILE"
    lake env lean --run scripts/TruthCoreConstants.lean TruthCore "$MODULES_FILE" > "$TEMP/constants.txt"
  else
    echo "==> listing TruthCore declarations"
    lake env lean --run scripts/TruthCoreConstants.lean TruthCore > "$TEMP/constants.txt"
  fi
  mapfile -t constants < "$TEMP/constants.txt"
  if [[ ${#constants[@]} -eq 0 ]]; then
    # Only reachable with --modules: an empty constant list would make lean4export export
    # everything, and there is nothing affected to check.
    echo "==> the listed modules define no TruthCore declarations; nothing to check"
    exit 0
  fi
  echo "==> exporting ${#constants[@]} TruthCore declarations with their dependencies"
  lake env "$LEAN4EXPORT_BIN" TruthCore -- "${constants[@]}" > "$EXPORT" 2> "$TEMP/export.err"
fi
# A Lean panic (for example an unparsable or missing constant name) prints and continues, so
# reject any exporter diagnostics instead of checking a partial export.
if [[ -s "$TEMP/export.err" ]]; then
  cat "$TEMP/export.err" >&2
  echo "lean4export reported errors; refusing to check a partial export" >&2
  exit 1
fi

cat > "$CONFIG" <<EOF
{
  "export_file_path": "$EXPORT",
  "use_stdin": false,
  "permitted_axioms": [
    "propext",
    "Classical.choice",
    "Quot.sound",
    "Lean.trustCompiler"
  ],
  "unpermitted_axiom_hard_error": false,
  "nat_extension": true,
  "string_extension": true,
  "print_success_message": true
}
EOF

echo "==> checking TruthCore with NanoDa ($MODE)"
"$NANODA_BIN" "$CONFIG"
