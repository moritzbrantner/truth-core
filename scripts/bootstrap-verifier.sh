#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$ROOT/scripts/verifier-pins.env"

WORK="${TRUTH_CORE_VERIFIER_HOME:-$HOME/.cache/truth-core-verifier}"
mkdir -p "$WORK" "$WORK/bin"

need() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "missing required build tool: $1" >&2
    exit 2
  }
}

need git
need lake
need cargo
need go

clone_at() {
  local url="$1"
  local rev="$2"
  local dir="$3"

  if [[ ! -d "$dir/.git" ]]; then
    git clone --filter=blob:none --no-checkout "$url" "$dir"
  fi

  if [[ "$(git -C "$dir" rev-parse HEAD 2>/dev/null || true)" != "$rev" ]]; then
    git -C "$dir" fetch --depth=1 origin "$rev"
    git -C "$dir" checkout --detach "$rev"
  fi
}

echo "==> comparator $COMPARATOR_REV"
clone_at https://github.com/leanprover/comparator.git "$COMPARATOR_REV" "$WORK/comparator"
(
  cd "$WORK/comparator"
  lake build comparator
)

echo "==> lean4export $LEAN4EXPORT_REV (matches truth-core Lean 4.32.0)"
clone_at https://github.com/leanprover/lean4export.git "$LEAN4EXPORT_REV" "$WORK/lean4export"
(
  cd "$WORK/lean4export"
  lake build lean4export
)

echo "==> landrun $LANDRUN_REV"
clone_at https://github.com/Zouuup/landrun.git "$LANDRUN_REV" "$WORK/landrun"
(
  cd "$WORK/landrun"
  go build -o "$WORK/bin/landrun" ./cmd/landrun
)

echo "==> nanoda $NANODA_REV"
clone_at https://github.com/ammkrn/nanoda_lib.git "$NANODA_REV" "$WORK/nanoda_lib"
(
  cd "$WORK/nanoda_lib"
  cargo build --release
)

cat <<SUMMARY
verifier ready in $WORK
  comparator:  $WORK/comparator/.lake/build/bin/comparator
  lean4export: $WORK/lean4export/.lake/build/bin/lean4export
  landrun:     $WORK/bin/landrun
  nanoda:      $WORK/nanoda_lib/target/release/nanoda_bin
SUMMARY
