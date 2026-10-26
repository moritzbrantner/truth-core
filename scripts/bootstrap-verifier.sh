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

  local resolved
  resolved="$(git -C "$dir" rev-parse --verify "$rev^{commit}" 2>/dev/null || true)"
  if [[ -z "$resolved" || "$(git -C "$dir" rev-parse HEAD 2>/dev/null || true)" != "$resolved" ]]; then
    if [[ "$rev" == v* ]]; then
      git -C "$dir" fetch --depth=1 origin tag "$rev"
    else
      git -C "$dir" fetch --depth=1 origin "$rev"
    fi
    git -C "$dir" checkout --detach FETCH_HEAD
  fi
}

# lean4export tags one release per Lean version; follow the exact toolchain
# pinned in lean-toolchain (the version the Mathlib release in
# lake-manifest.json requires). Re-run this script after every toolchain bump:
# an export built for another Lean version fails with "incompatible header".
LEAN_VERSION="$(cd "$ROOT" && lean --version | sed -E 's/^Lean \(version ([^,]+),.*/\1/')"
LEAN4EXPORT_REV="v$LEAN_VERSION"

echo "==> truth-core Rust comparator"
cargo build --locked --release --manifest-path "$ROOT/verifier/Cargo.toml" --target-dir "$WORK/rust-target"

echo "==> lean4export $LEAN4EXPORT_REV (matches truth-core Lean $LEAN_VERSION)"
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
  comparator:  $WORK/rust-target/release/truth-core-comparator
  lean4export: $WORK/lean4export/.lake/build/bin/lean4export
  landrun:     $WORK/bin/landrun
  nanoda:      $WORK/nanoda_lib/target/release/nanoda_bin
SUMMARY
