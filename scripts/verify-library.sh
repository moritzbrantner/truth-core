#!/usr/bin/env bash
set -euo pipefail

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
echo "==> exporting TruthCore"
lake env "$LEAN4EXPORT_BIN" TruthCore > "$EXPORT"

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

echo "==> checking TruthCore with NanoDa"
"$NANODA_BIN" "$CONFIG"
