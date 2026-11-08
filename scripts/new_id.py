#!/usr/bin/env python3
"""Mint new corpus ids: opaque uuid4s (owner decision 2026-11-07).

    python3 scripts/new_id.py        # one id
    python3 scripts/new_id.py 5      # five ids

Never mint a readable id: put the human name in the record's `label`
(unique within its kind, no id-like text, sense-tagged terms). A new record's
file is `corpus/<kind>/<uuid>.json`; a new result's Comparator config is
`results/<uuid>/comparator.json`.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from corpus_ids import new_uuid  # noqa: E402


def main(argv: list[str]) -> int:
    count = int(argv[0]) if argv else 1
    for _ in range(count):
        print(new_uuid())
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
