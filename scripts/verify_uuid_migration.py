#!/usr/bin/env python3
"""Prove a uuid migration lossless against a pre-migration revision.

    python3 scripts/verify_uuid_migration.py --base <PRE-MIGRATION-REV> [--outputs]

1. Records: every record of the base revision maps to exactly one record of the
   working tree with the same kind and file, and mapping every uuid of the new
   record back to its legacy id (and dropping `label`/`legacy_id`) gives back
   the old record exactly. Equal records with equal references make the two
   reference graphs isomorphic under the legacy_id bijection. The same holds
   for the tooling data the migration rewrites (bundle audits up to their
   carried-over review hashes, contracts, exemptions, test data).
2. With --outputs: `corpus.py frontier --json`, `frontier --routes --json`,
   `thickness --json` and `thickness --queue --json` of the base revision
   (run in a temporary worktree) equal those of the working tree once uuids are
   mapped back to legacy ids. List order is compared as a multiset, since id
   order changes with the ids themselves.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))

from corpus_ids import KIND_DIRS, PROSE_UUID_RE, is_uuid  # noqa: E402
from migrate_uuid import AUX_FIELDS  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
IDENTITY_KEYS = ("label", "legacy_id")


def git(*args: str, cwd: Path = ROOT) -> str:
    return subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True, text=True).stdout


def base_files(base: str, prefix: str) -> dict[str, str]:
    names = git("ls-tree", "-r", "--name-only", base, "--", prefix).split()
    out = {}
    for name in names:
        if name.endswith(".json"):
            out[name] = git("show", f"{base}:{name}")
    return out


def back_map(tree_root: Path) -> dict[str, str]:
    """uuid -> legacy id over the working tree."""
    table: dict[str, str] = {}
    for directory in KIND_DIRS:
        for path in (tree_root / "corpus" / directory).glob("*.json"):
            data = json.loads(path.read_text(encoding="utf-8"))
            records = data.get("passages", []) if directory == "passages" else [data]
            for record in records:
                if isinstance(record, dict) and is_uuid(record.get("id")) and record.get("legacy_id"):
                    if record["id"] in table and table[record["id"]] != record["legacy_id"]:
                        raise SystemExit(f"uuid {record['id']} has two legacy ids")
                    table[record["id"]] = record["legacy_id"]
    return table


def unmap(value: Any, table: dict[str, str], *, drop_identity: bool) -> Any:
    """Map uuids back to legacy ids; `drop_identity` drops a record's own label/legacy_id."""
    if isinstance(value, dict):
        record = drop_identity and is_uuid(value.get("id")) and "legacy_id" in value
        return {
            (table.get(key, key) if isinstance(key, str) else key): unmap(item, table, drop_identity=drop_identity)
            for key, item in value.items()
            if not (record and key in IDENTITY_KEYS)
        }
    if isinstance(value, list):
        return [unmap(item, table, drop_identity=drop_identity) for item in value]
    if isinstance(value, str) and is_uuid(value):
        return table.get(value, value)
    if isinstance(value, str) and not drop_identity:
        # Report prose that embeds ids ("rivals deny it: <uuid>, <uuid>").
        return PROSE_UUID_RE.sub(lambda match: table.get(match.group(0), match.group(0)), value)
    return value


def canonical(value: Any) -> Any:
    if isinstance(value, dict):
        return {key: canonical(item) for key, item in value.items()}
    if isinstance(value, list):
        items = [canonical(item) for item in value]
        return sorted(items, key=lambda item: json.dumps(item, sort_keys=True, ensure_ascii=False))
    return value


def strip_review_hashes(value: Any) -> Any:
    if isinstance(value, dict):
        return {key: strip_review_hashes(item) for key, item in value.items() if key != "reviewed_sha256"}
    if isinstance(value, list):
        return [strip_review_hashes(item) for item in value]
    return value


def check_records(base: str) -> list[str]:
    problems: list[str] = []
    table = back_map(ROOT)
    legacy_to_uuid: dict[tuple[str, str], str] = {}
    for uid, legacy in table.items():
        legacy_to_uuid.setdefault(("*", legacy + ":" + uid), uid)
    if len(set(table)) != len(table):
        problems.append("uuid collision")
    old = base_files(base, "corpus")
    counts: dict[str, int] = {}
    for name, text in old.items():
        path = ROOT / name
        if not path.is_file():
            problems.append(f"{name}: missing after migration")
            continue
        before = json.loads(text)
        after = unmap(json.loads(path.read_text(encoding="utf-8")), table, drop_identity=True)
        if before != after:
            problems.append(f"{name}: differs after mapping uuids back")
        directory = Path(name).parent.name
        counts[directory] = counts.get(directory, 0) + (len(before.get("passages", [])) if directory == "passages" else 1)
    new_names = {
        str(path.relative_to(ROOT)) for path in (ROOT / "corpus").rglob("*.json")
    }
    extra = sorted(new_names - set(old))
    for name in extra:
        problems.append(f"{name}: not in base")
    for pattern in AUX_FIELDS:
        for path in sorted(ROOT.glob(pattern)):
            name = str(path.relative_to(ROOT))
            try:
                before = json.loads(git("show", f"{base}:{name}"))
            except subprocess.CalledProcessError:
                continue
            after = unmap(json.loads(path.read_text(encoding="utf-8")), table, drop_identity=False)
            if strip_review_hashes(before) != strip_review_hashes(after):
                problems.append(f"{name}: differs after mapping uuids back")
    print(f"records: {sum(counts.values())} compared, {len(table)} uuid<->legacy pairs, bijective")
    for directory in sorted(counts):
        print(f"  {directory}: {counts[directory]}")
    return problems


OUTPUTS = (
    ("frontier", ["frontier", "--json"]),
    ("routes", ["frontier", "--routes", "--json"]),
    ("thickness", ["thickness", "--json"]),
    ("queue", ["thickness", "--queue", "--json"]),
)


def run_outputs(tree: Path) -> dict[str, Any]:
    out = {}
    for name, args in OUTPUTS:
        result = subprocess.run([sys.executable, "scripts/corpus.py", *args], cwd=tree,
                                capture_output=True, text=True, check=True)
        out[name] = json.loads(result.stdout)
    return out


def check_outputs(base: str) -> list[str]:
    problems = []
    table = back_map(ROOT)
    with tempfile.TemporaryDirectory() as temporary:
        tree = Path(temporary) / "base"
        git("worktree", "add", "--detach", str(tree), base)
        try:
            before = run_outputs(tree)
        finally:
            git("worktree", "remove", "--force", str(tree))
    after = run_outputs(ROOT)
    for name, _ in OUTPUTS:
        old = canonical(before[name])
        new = canonical(unmap(after[name], table, drop_identity=False))
        old.pop("input_identity", None) if isinstance(old, dict) else None
        new.pop("input_identity", None) if isinstance(new, dict) else None
        if old != new:
            problems.append(f"{name}: output differs after mapping uuids back")
        else:
            print(f"output {name}: equal after mapping uuids back")
    return problems


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--base", required=True, help="pre-migration revision")
    parser.add_argument("--outputs", action="store_true", help="also compare frontier and thickness outputs")
    args = parser.parse_args(argv)
    problems = check_records(args.base)
    if args.outputs:
        problems += check_outputs(args.base)
    for problem in problems[:50]:
        print(f"problem: {problem}")
    if problems:
        print(f"{len(problems)} problem(s)")
        return 1
    print("lossless: every record and reference maps back to the base revision")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
