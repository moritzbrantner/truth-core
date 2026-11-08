#!/usr/bin/env python3
"""Convert corpus identity to opaque UUIDs (owner decision 2026-11-07).

    python3 scripts/migrate_uuid.py           # report what would change
    python3 scripts/migrate_uuid.py --write   # rewrite the tree in place

Every record whose id is not a uuid gets

    id        = uuid5(NAMESPACE, "<kind>:<old id>")   (scripts/corpus_ids.py)
    label     = a display label derived from the old id (kept if already set)
    legacy_id = the old id (an alias that never changes)

and every reference field (``corpus_ids.REFERENCE_FIELDS``) that names a known
legacy id is rewritten to that record's uuid. A reference to an unknown id is
left as it is, so ``corpus.py check`` still reports it.

The conversion is deterministic and idempotent: rerunning it on a migrated tree
changes nothing, and running it after merging a branch converts the branch's
new legacy-id records the same way on every machine. See
docs/notes/uuid-migration.md for converting an in-flight branch.

Besides the corpus it rewrites the tooling data that names corpus ids:
bundle audits (docs/notes/*-migration.json, whose reviewed hashes are carried
over when the record was unchanged before migration), expression contracts
(scripts/contracts), unused-premise exemptions and test data. Prose that cites
legacy ids stays as text: legacy ids are aliases that resolve.

File names are kept: records stay at their current paths, and Comparator
configs stay at results/<legacy id>/comparator.json (the result record's
`comparator_config` names the path). New records use `<uuid>.json` and
`results/<uuid>/comparator.json`.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))

from corpus_ids import (  # noqa: E402
    DIR_OF_KIND,
    SenseIndex,
    KIND_DIRS,
    is_uuid,
    keyed_dicts,
    legacy_uuid,
    reference_slots,
)
from uuid_labels import Labeler, make_unique  # noqa: E402

LABEL_ORDER = ("source", "passage", "statement", "definition", "disambiguation", "claim", "inference",
               "argument", "result", "relation", "candidate", "attempt", "model", "configuration")
CLEANUP_JSON = "docs/notes/label-cleanup.json"
CLEANUP_MD = "docs/notes/label-cleanup.md"

ROOT = Path(__file__).resolve().parents[1]

# Tooling data outside corpus/ that names corpus ids: path glob -> field spec.
# A spec maps a key path (as in corpus_ids.REFERENCE_FIELDS) to a kind; the
# special target "@kind-dir" takes the kind from a sibling "kind" directory name.
AUX_FIELDS: dict[str, tuple[tuple[tuple[str, ...], Any], ...]] = {
    "docs/notes/*-migration.json": (
        (("result_id",), "result"),
        (("consumer_result_ids", "[]"), "result"),
        (("root",), "statement"),
        (("designated_route",), "argument"),
        (("records", "[]", "id"), "@kind-dir"),
    ),
    "scripts/contracts/*.json": ((("result_id",), "result"),),
    "corpus/sense-index-allowlist.json": (),
    "scripts/unused-premise-exemptions.json": (
        (("exemptions", "[]", "result_id"), "result"),
        (("exemptions", "[]", "statement_ids", "[]"), "statement"),
    ),
    "scripts/testdata/objective-truth-pilot.json": (
        (("statement_ids", "[]"), "statement"),
        (("argument_ids", "[]"), "argument"),
        (("cases", "[]", "result_ids", "[]"), "result"),
        (("cases", "[]", "expected_established", "[]"), "statement"),
    ),
}
# Dict keys that are result ids.
AUX_KEYED: dict[str, tuple[tuple[str, ...], str]] = {
    "docs/notes/*-migration.json": (("contract_baselines",), "result"),
    # Sense-indexed terms (#1235): allowlisted arguments; sense uuids stay as they are.
    "corpus/sense-index-allowlist.json": (("arguments",), "argument"),
}


def dump_like(original: str, data: Any) -> str:
    """Serialize `data` in the layout of `original` (indented or one line)."""
    ascii_only = "\\u" in original and all(ord(ch) < 128 for ch in original)
    indent = 2 if original.lstrip().startswith("{\n") or "\n " in original else None
    return json.dumps(data, indent=indent, ensure_ascii=ascii_only) + "\n"


def with_identity(record: dict[str, Any], kind: str) -> dict[str, Any]:
    """`record` with a uuid id, label and legacy_id placed right after id."""
    legacy = record["id"]
    out: dict[str, Any] = {"id": legacy_uuid(kind, legacy)}
    out["label"] = record.get("label")  # filled from prose by uuid_labels.Labeler
    out["legacy_id"] = legacy
    for key, value in record.items():
        if key not in out:
            out[key] = value
    return out


class Migration:
    def __init__(self, root: Path) -> None:
        self.root = root
        # legacy id -> kind -> uuid, from records already converted or about to be.
        self.legacy: dict[str, dict[str, str]] = {}
        self.files: dict[Path, tuple[str, Any]] = {}  # path -> (original text, data)
        self.counts: dict[str, int] = {}
        self.references = 0
        self.cleanup: list[dict[str, Any]] = []
        self.converted: dict[str, set[str]] = {}
        self.generated = 0

    # -- loading ---------------------------------------------------------
    def load(self) -> None:
        corpus = self.root / "corpus"
        for directory, kind in KIND_DIRS.items():
            for path in sorted((corpus / directory).glob("*.json")):
                text = path.read_text(encoding="utf-8")
                data = json.loads(text)
                self.files[path] = (text, data)
                if not isinstance(data, dict):
                    continue
                records = data.get("passages", []) if kind == "passage" else [data]
                for record in records:
                    if not isinstance(record, dict) or not isinstance(record.get("id"), str):
                        continue
                    record_id = record["id"]
                    legacy = record_id if not is_uuid(record_id) else record.get("legacy_id")
                    if isinstance(legacy, str) and legacy:
                        uid = record_id if is_uuid(record_id) else legacy_uuid(kind, legacy)
                        self.legacy.setdefault(legacy, {})[kind] = uid

    def lookup(self, value: str, kinds: tuple[str, ...]) -> str | None:
        if is_uuid(value):
            return None
        table = self.legacy.get(value, {})
        for kind in kinds:
            if kind in table:
                return table[kind]
        return None

    def rewrite_slots(self, slots) -> bool:
        changed = False
        for container, key, kinds in slots:
            new = self.lookup(container[key], kinds)
            if new is not None:
                container[key] = new
                self.references += 1
                changed = True
        return changed

    # -- corpus ------------------------------------------------------------
    def migrate_corpus(self) -> dict[Path, str]:
        for path, (text, data) in list(self.files.items()):
            if not isinstance(data, dict):
                continue
            kind = KIND_DIRS[path.parent.name]
            if kind == "passage":
                self.rewrite_slots(reference_slots("passage-file", data))
                passages = data.get("passages", [])
                for index, passage in enumerate(passages):
                    if isinstance(passage, dict) and isinstance(passage.get("id"), str) and not is_uuid(passage["id"]):
                        passages[index] = with_identity(passage, kind)
                        self.converted.setdefault(kind, set()).add(passages[index]["id"])
                        self.counts[kind] = self.counts.get(kind, 0) + 1
            else:
                if isinstance(data.get("id"), str) and not is_uuid(data["id"]):
                    data = with_identity(data, kind)
                    self.converted.setdefault(kind, set()).add(data["id"])
                    self.counts[kind] = self.counts.get(kind, 0) + 1
                self.rewrite_slots(reference_slots(kind, data))
                for node, target in keyed_dicts(kind, data):
                    renamed = {(self.lookup(key, (target,)) or key): value for key, value in node.items()}
                    if list(renamed) != list(node):
                        self.references += sum(1 for a, b in zip(renamed, node) if a != b)
                        node.clear()
                        node.update(renamed)
            self.files[path] = (text, data)
        self.label_records()
        out: dict[Path, str] = {}
        for path, (text, data) in self.files.items():
            if isinstance(data, dict):
                rendered = dump_like(text, data)
                if rendered != text and json.loads(text) != data:
                    out[path] = rendered
        return out

    # -- tooling data ----------------------------------------------------------
    def migrate_aux(self, written: dict[Path, str]) -> dict[Path, str]:
        out: dict[Path, str] = {}
        for pattern, fields in AUX_FIELDS.items():
            for path in sorted(self.root.glob(pattern)):
                text = path.read_text(encoding="utf-8")
                data = json.loads(text)
                changed = False
                for field_path, target in fields:
                    from corpus_ids import _slots
                    for container, key, parent in _slots(data, field_path):
                        if target == "@kind-dir":
                            kind = KIND_DIRS.get(parent.get("kind")) if isinstance(parent, dict) else None
                            kinds = (kind,) if kind else ()
                        else:
                            kinds = (target,)
                        new = self.lookup(container[key], kinds) if kinds else None
                        if new is not None:
                            container[key] = new
                            changed = True
                keyed = AUX_KEYED.get(pattern)
                if keyed:
                    node: Any = data
                    for step in keyed[0]:
                        node = node.get(step) if isinstance(node, dict) else None
                    if isinstance(node, dict):
                        for key in list(node):
                            new = self.lookup(key, (keyed[1],))
                            if new is not None:
                                node[new] = node.pop(key)
                                changed = True
                if pattern == "docs/notes/*-migration.json":
                    changed |= self.carry_review_hashes(data, written)
                if changed:
                    rendered = dump_like(text, data)
                    if rendered != text:
                        out[path] = rendered
        return out

    def carry_review_hashes(self, audit: dict[str, Any], written: dict[Path, str]) -> bool:
        """A record reviewed at its pre-migration bytes stays reviewed after an identity-only rewrite."""
        changed = False
        for row in audit.get("records", []):
            path = self.root / row.get("path", "")
            if path not in written:
                continue
            old = hashlib.sha256(path.read_bytes()).hexdigest()
            if row.get("reviewed_sha256") == old:
                row["reviewed_sha256"] = hashlib.sha256(written[path].encode("utf-8")).hexdigest()
                changed = True
        return changed

    # -- labels ------------------------------------------------------------------
    def label_records(self) -> None:
        """Give every record without a label one derived from its prose, unique per kind."""
        records: dict[str, dict[str, dict[str, Any]]] = {}
        for path, (_, data) in self.files.items():
            kind = KIND_DIRS[path.parent.name]
            if not isinstance(data, dict):
                continue
            items = data.get("passages", []) if kind == "passage" else [data]
            for record in items:
                if isinstance(record, dict) and isinstance(record.get("id"), str):
                    if kind == "passage":
                        record = {**record, "source_id": data.get("snapshot", {}).get("source_id")}
                    records.setdefault(kind, {})[record["id"]] = record
        self.records = records
        senses = SenseIndex(records.get("definition", {}), records.get("disambiguation", {}),
                            records.get("statement", {}), records.get("argument", {}))
        labeler = Labeler(records, senses)
        for kind in LABEL_ORDER:
            items = records.get(kind, {})
            fixed = {record_id for record_id, record in items.items() if record.get("label")}
            # A record converted now that already had a label (authored on a branch
            # before the migration) keeps it; a missing sense tag is listed like
            # the migration's own compromises.
            for record_id in sorted(fixed & self.converted.get(kind, set())):
                if senses.untagged(kind, items[record_id]["label"], items[record_id]):
                    self.cleanup.append({
                        "kind": kind, "id": record_id, "legacy_id": items[record_id].get("legacy_id"),
                        "label": items[record_id]["label"], "flags": ["untagged-sense"],
                    })
            fresh = {record_id: labeler.make(kind, record) for record_id, record in items.items()
                     if not record.get("label")}
            if not fresh:
                continue
            labels = {**{record_id: items[record_id]["label"] for record_id in fixed}, **fresh}
            flags = {record_id: labeler.flags[(kind, record_id)] for record_id in fresh}
            unique = make_unique(labels, fixed, flags)
            for record_id in fresh:
                items[record_id]["label"] = unique[record_id]
                self.generated += 1
                if not flags[record_id]:
                    continue
                self.cleanup.append({
                    "kind": kind, "id": record_id, "legacy_id": items[record_id].get("legacy_id"),
                    "label": unique[record_id], "flags": sorted(flags[record_id]),
                })
        # Passage records above were copies (for source_id); write labels back.
        for path, (_, data) in self.files.items():
            if KIND_DIRS[path.parent.name] == "passage" and isinstance(data, dict):
                for passage in data.get("passages", []):
                    if isinstance(passage, dict) and not passage.get("label"):
                        passage["label"] = records["passage"][passage["id"]]["label"]

    def cleanup_report(self) -> dict[Path, str]:
        path = self.root / CLEANUP_JSON
        existing = json.loads(path.read_text(encoding="utf-8")) if path.is_file() else []
        known = {entry["id"] for entry in existing}
        entries = existing + [entry for entry in self.cleanup if entry["id"] not in known]
        entries.sort(key=lambda entry: (entry["kind"], entry["label"], entry["id"]))
        return {
            path: json.dumps(entries, indent=1, ensure_ascii=False) + "\n",
            self.root / CLEANUP_MD: cleanup_markdown(entries, self.generated),
        }

    def run(self, write: bool) -> dict[Path, str]:
        self.load()
        corpus = self.migrate_corpus()
        aux = self.migrate_aux(corpus)
        changes = {**corpus, **aux}
        if self.cleanup:
            changes.update(self.cleanup_report())
        if write:
            for path, text in changes.items():
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")
        return changes


CLEANUP_FLAGS = {
    "truncated": "the prose was cut to fit the 100-character limit",
    "duplicate": "numbered to stay unique within its kind",
    "ids-replaced": "readable-id tokens in the prose were replaced by their words",
    "from-legacy-id": "part of the label (an argument's route, or a fallback) came from the old id",
    "fallback": "no prose to derive a label from",
    "untagged-sense": "a term with several linked senses (or an undeterminable sense) is untagged",
}


def cleanup_markdown(entries: list[dict[str, Any]], generated: int | None) -> str:
    from collections import Counter
    flags = Counter(flag for entry in entries for flag in entry["flags"])
    kinds = Counter(entry["kind"] for entry in entries if entry["flags"])
    lines = [
        "# Label clean-up (uuid migration)",
        "",
        "The uuid migration (`scripts/migrate_uuid.py`, docs/notes/uuid-migration.md) derived a",
        "display label for every record from its prose. Labels are mechanical: each was made by",
        "`scripts/uuid_labels.py`, not written by a person. This list names the labels whose",
        "derivation needed a compromise, so they can be fixed in follow-ups. The machine-readable",
        "list is `docs/notes/label-cleanup.json` (`kind`, `id`, `legacy_id`, `label`, `flags`).",
        "",
        "`corpus.py check` treats its `untagged-sense` entries as the allowlist for the sense-tag",
        "rule: they are warnings, while a new record with an untagged linked-sense term is an error.",
        "Editing a label is safe: ids never change, and the label only has to stay unique within",
        "its kind, free of id-like text and at most 100 characters. The list may only shrink",
        "(#1233): CI runs `python3 scripts/label_cleanup.py check --base <base>`. After fixing",
        "labels, `python3 scripts/label_cleanup.py prune` removes the entries that now pass.",
        "",
        (f"Labels generated in the migration: {generated}; flagged: {len(entries)}." if generated is not None
         else f"Flagged labels remaining: {len(entries)}."),
        "",
        "| flag | count | meaning |",
        "| --- | ---: | --- |",
    ]
    for flag, meaning in CLEANUP_FLAGS.items():
        lines.append(f"| `{flag}` | {flags.get(flag, 0)} | {meaning} |")
    lines += ["", "Flagged labels per kind:", ""]
    for kind, count in sorted(kinds.items()):
        lines.append(f"- {kind}: {count}")
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--write", action="store_true", help="rewrite files in place")
    parser.add_argument("--root", type=Path, default=ROOT, help=argparse.SUPPRESS)
    args = parser.parse_args(argv)
    migration = Migration(args.root.resolve())
    changes = migration.run(args.write)
    verb = "rewrote" if args.write else "would rewrite"
    print(f"{verb} {len(changes)} files; {migration.references} references")
    for kind in sorted(migration.counts):
        print(f"  {DIR_OF_KIND[kind]}: {migration.counts[kind]} ids converted")
    if not changes:
        print("tree already uses uuid identity")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
