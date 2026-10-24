#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
JOBS="${TRUTH_CORE_VERIFY_JOBS:-$(nproc)}"

mapfile -t results < <(python3 "$ROOT/scripts/corpus.py" results | sed '/^$/d')

# Build every challenge and solution module in one Lake run first. The default target does not
# include the challenges, and parallel Comparator runs would otherwise race to write shared .olean
# files; afterwards each sandboxed `lake build` inside a run only replays finished builds.
mapfile -t modules < <(cd "$ROOT" && python3 -c '
import json, sys
for result in sys.argv[1:]:
    config = json.load(open(f"results/{result}/comparator.json"))
    print(config["challenge_module"])
    print(config["solution_module"])
' "${results[@]}" | sort -u)
if ! build_log="$(cd "$ROOT" && lake build "${modules[@]}" 2>&1)"; then
  printf '%s\n' "$build_log" >&2
  exit 1
fi

# Each result runs its own Comparator; output is buffered per result so the log stays readable.
# xargs exits non-zero when any result fails, and every failure prints its full output.
export VERIFY_RESULT="$ROOT/scripts/verify-result.sh"
printf '%s\n' "${results[@]}" | xargs -r -P "$JOBS" -I{} bash -c '
  if out="$("$VERIFY_RESULT" "$1" 2>&1)"; then
    printf "%s\n" "$out"
  else
    printf "%s\n" "$out" >&2
    echo "::error::Comparator verification failed for $1" >&2
    exit 1
  fi
' _ {}
echo "verified ${#results[@]} results"
