#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

while IFS= read -r result_id; do
  [[ -n "$result_id" ]] || continue
  "$ROOT/scripts/verify-result.sh" "$result_id"
done < <(python3 "$ROOT/scripts/corpus.py" results)
