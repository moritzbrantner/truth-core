#!/usr/bin/env bash
set -euo pipefail

# Check the built TruthCore library with NanoDa.
#
#   scripts/verify-library.sh          scoped: every TruthCore declaration together with every
#                                      declaration it depends on (Mathlib, Lean core), and nothing else
#   scripts/verify-library.sh --full   everything TruthCore imports, including Mathlib declarations
#                                      that no TruthCore declaration uses
#
# The scoped check trusts nothing it does not check: lean4export exports the full dependency
# closure of the listed constants. The full check adds only unused library declarations; CI runs
# it once per Mathlib/toolchain/NanoDa pin and set of external imports (docs/axiom-policy.md).

usage() {
  echo "usage: $0 [--full]" >&2
  exit 2
}

MODE=scoped
case "${1:-}" in
  "") ;;
  --full) MODE=full ;;
  *) usage ;;
esac
[[ $# -le 1 ]] || usage

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
  echo "==> listing TruthCore declarations"
  lake env lean --run scripts/TruthCoreConstants.lean TruthCore > "$TEMP/constants.txt"
  mapfile -t constants < "$TEMP/constants.txt"
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
