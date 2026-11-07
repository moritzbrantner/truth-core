#!/usr/bin/env python3
"""Ratchet for the label clean-up list (issue #1233, section C).

docs/notes/label-cleanup.json lists the labels the uuid migration made
mechanically and with a compromise (truncated, numbered duplicate, id words,
route from the old id, or a term without its sense tag). The list may only
shrink:

    python3 scripts/label_cleanup.py check --base <REV>   # CI: no entry added
    python3 scripts/label_cleanup.py passing              # entries to remove
    python3 scripts/label_cleanup.py prune                # remove them, regenerate the .md

An entry passes once its record's label was rewritten (it differs from the
recorded mechanical label) and the label has no untagged linked-sense term, or
once the record is gone. `corpus.py check` warns about each passing entry so it
is removed; its `untagged-sense` entries are the allowlist of the sense-tag rule.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))

from corpus_ids import SenseIndex, iter_records  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
CLEANUP = "docs/notes/label-cleanup.json"


def load(root: Path = ROOT) -> list[dict[str, Any]]:
    path = root / CLEANUP
    return json.loads(path.read_text(encoding="utf-8")) if path.is_file() else []


def passing(root: Path = ROOT, entries: list[dict[str, Any]] | None = None) -> list[tuple[dict[str, Any], str]]:
    """(entry, reason) for every entry that no longer needs to be listed."""
    entries = load(root) if entries is None else entries
    records: dict[str, tuple[str, dict[str, Any]]] = {}
    by_kind: dict[str, dict[str, dict[str, Any]]] = {}
    for kind, _, record in iter_records(root):
        if isinstance(record.get("id"), str):
            records[record["id"]] = (kind, record)
            by_kind.setdefault(kind, {})[record["id"]] = record
    senses = SenseIndex(by_kind.get("definition", {}), by_kind.get("disambiguation", {}))
    out = []
    for entry in entries:
        found = records.get(entry["id"])
        if found is None:
            out.append((entry, "the record no longer exists"))
            continue
        kind, record = found
        label = record.get("label", "")
        untagged = senses.untagged(kind, label, record)
        rewritten = label != entry.get("label")
        only_sense = set(entry.get("flags", [])) <= {"untagged-sense"}
        if not untagged and (rewritten or only_sense):
            out.append((entry, "label rewritten" if rewritten else "sense tags complete"))
    return out


def base_entries(base: str, root: Path = ROOT) -> list[dict[str, Any]] | None:
    completed = subprocess.run(["git", "-C", str(root), "show", f"{base}:{CLEANUP}"],
                               capture_output=True, text=True)
    if completed.returncode != 0:
        return None
    return json.loads(completed.stdout)


def added_entries(base: str, root: Path = ROOT) -> list[dict[str, Any]]:
    """Entries present now but not at `base` (none when base predates the list)."""
    before = base_entries(base, root)
    if before is None:
        return []
    known = {(entry["id"], tuple(entry.get("flags", []))) for entry in before}
    old_flags = {entry["id"]: set(entry.get("flags", [])) for entry in before}
    return [entry for entry in load(root)
            if (entry["id"], tuple(entry.get("flags", []))) not in known
            and not set(entry.get("flags", [])) <= old_flags.get(entry["id"], set())]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    check = sub.add_parser("check", help="fail if an entry was added since BASE")
    check.add_argument("--base", required=True)
    sub.add_parser("passing", help="list entries that pass and should be removed")
    sub.add_parser("prune", help="remove passing entries and regenerate docs/notes/label-cleanup.md")
    args = parser.parse_args(argv)
    if args.command == "prune":
        from migrate_uuid import CLEANUP_MD, cleanup_markdown

        done = {entry["id"] for entry, _ in passing()}
        kept = [entry for entry in load() if entry["id"] not in done]
        (ROOT / CLEANUP).write_text(json.dumps(kept, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
        (ROOT / CLEANUP_MD).write_text(cleanup_markdown(kept, None), encoding="utf-8")
        print(f"removed {len(done)} passing entries; {len(kept)} remain")
        return 0
    if args.command == "passing":
        for entry, reason in passing():
            print(f"{entry['kind']} {entry['id']} ({reason}): remove from {CLEANUP}")
        return 0
    added = added_entries(args.base)
    for entry in added:
        print(f"label clean-up list grew: {entry['kind']} {entry['id']} {entry.get('label')!r} "
              f"{entry.get('flags')}; fix the label instead of listing it")
    done = passing()
    for entry, reason in done:
        print(f"note: {entry['kind']} {entry['id']} passes ({reason}); remove it from {CLEANUP}")
    print(f"label clean-up list: {len(load())} entries; {len(added)} added since {args.base}; "
          f"{len(done)} passing")
    return 1 if added else 0


if __name__ == "__main__":
    raise SystemExit(main())
