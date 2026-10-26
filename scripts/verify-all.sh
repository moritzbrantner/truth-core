#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
JOBS="${TRUTH_CORE_VERIFY_JOBS:-$(nproc)}"

usage() {
  echo "usage: $0 [--results-file FILE] [--shard INDEX/COUNT]" >&2
  echo "  --results-file  verify only the result IDs listed in FILE (default: every result)" >&2
  echo "  --shard         verify only shard INDEX (0-based) of COUNT balanced shards" >&2
  exit 2
}

RESULTS_FILE=""
SHARD=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --results-file) [[ $# -ge 2 ]] || usage; RESULTS_FILE="$2"; shift 2 ;;
    --shard) [[ $# -ge 2 && "$2" =~ ^[0-9]+/[1-9][0-9]*$ ]] || usage; SHARD="$2"; shift 2 ;;
    *) usage ;;
  esac
done

if [[ -n "$RESULTS_FILE" ]]; then
  [[ -f "$RESULTS_FILE" ]] || { echo "missing results file: $RESULTS_FILE" >&2; exit 2; }
  mapfile -t results < <(sed '/^$/d' "$RESULTS_FILE")
else
  all_ids="$(python3 "$ROOT/scripts/corpus.py" results)"
  mapfile -t results < <(printf '%s\n' "$all_ids" | sed '/^$/d')
fi
if [[ -n "$SHARD" ]]; then
  SHARD_LIST="$(mktemp)"
  trap 'rm -f "$SHARD_LIST"' EXIT
  printf '%s\n' "${results[@]}" > "$SHARD_LIST"
  # Run the selector on its own so that a failure stops the script (a process substitution would
  # hide its exit status and silently verify nothing).
  shard_ids="$(python3 "$ROOT/scripts/affected_results.py" shard \
    --index "${SHARD%/*}" --count "${SHARD#*/}" --results-file "$SHARD_LIST")"
  mapfile -t results < <(printf '%s\n' "$shard_ids" | sed '/^$/d')
fi
if [[ ${#results[@]} -eq 0 ]]; then
  echo "verified 0 results"
  exit 0
fi

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
