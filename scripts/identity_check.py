"""Identity and label rules of `corpus.py check` (owner decisions 2026-11-07).

* Every record id is a uuid, unique across the corpus. A record converted from
  a readable id keeps it as `legacy_id`, which must be the alias its uuid5 was
  made from; legacy ids are unique within a kind.
* Every record has a `label`: a non-empty display name of at most 100
  characters, unique within its kind (case-insensitively), with no uuid-like
  or id-like text (`STMT-FOO`, `Q11-OLD-…`).
* A label term with a disambiguated sense that the record links carries its
  sense tag (`PRIOR_1`). An untagged term is a warning for a migrated record
  listed in docs/notes/label-cleanup.json (flag `untagged-sense`) and an error
  for every other record.

`truth check` enforces the same rules (verify_truth_cli.py checks parity).
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from corpus_ids import LABEL_MAX, SenseIndex, idlike_text, is_uuid, iter_records, legacy_uuid

CLEANUP = Path("docs/notes/label-cleanup.json")


class IdentityError(Exception):
    pass


def sense_allowlist(root: Path) -> set[str]:
    path = root / CLEANUP
    if not path.is_file():
        return set()
    return {entry["id"] for entry in json.loads(path.read_text(encoding="utf-8"))
            if "untagged-sense" in entry.get("flags", [])}


def _scan(root: Path) -> tuple[list[str], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []
    records = [(kind, path, record) for kind, path, record in iter_records(root)]
    seen: dict[str, str] = {}
    legacy: dict[tuple[str, str], str] = {}
    labels: dict[tuple[str, str], str] = {}
    by_kind: dict[str, dict[str, dict[str, Any]]] = {}
    for kind, path, record in records:
        where = str(path.relative_to(root))
        record_id = record.get("id")
        if not is_uuid(record_id):
            errors.append(f"{where}: {kind} id {record_id!r} is not a uuid; ids are opaque uuids "
                          "(python3 scripts/new_id.py), readable names go in label")
            continue
        if record_id in seen:
            errors.append(f"{where}: id {record_id} is also the id of a record in {seen[record_id]}")
        seen[record_id] = where
        by_kind.setdefault(kind, {})[record_id] = record
        alias = record.get("legacy_id")
        if alias is not None:
            if not isinstance(alias, str) or not alias or legacy_uuid(kind, alias) != record_id:
                errors.append(f"{where}: legacy_id {alias!r} is not the alias {record_id} was made from")
            elif (kind, alias) in legacy:
                errors.append(f"{where}: legacy_id {alias} is also used by {legacy[(kind, alias)]}")
            else:
                legacy[(kind, alias)] = where
        label = record.get("label")
        if not isinstance(label, str) or not label.strip():
            errors.append(f"{where}: {kind} {record_id} has no label")
            continue
        if len(label) > LABEL_MAX:
            errors.append(f"{where}: label is longer than {LABEL_MAX} characters")
        if label != label.strip():
            errors.append(f"{where}: label has surrounding whitespace")
        found = idlike_text(label)
        if found:
            errors.append(f"{where}: label contains id-like text {', '.join(found)}; labels name the thing")
        key = (kind, label.casefold())
        if key in labels:
            errors.append(f"{where}: label {label!r} is also the label of {labels[key]}; labels are unique per kind")
        else:
            labels[key] = where
    senses = SenseIndex(by_kind.get("definition", {}), by_kind.get("disambiguation", {}),
                        by_kind.get("statement", {}), by_kind.get("argument", {}))
    allowed = sense_allowlist(root)
    for kind, path, record in records:
        label = record.get("label")
        if not isinstance(label, str) or not is_uuid(record.get("id")):
            continue
        missing = senses.untagged(kind, label, record)
        if not missing:
            continue
        message = (f"{path.relative_to(root)}: label {label!r} uses {', '.join(missing)} without its sense tag "
                   "(e.g. PRIOR_1) although the record links a disambiguated sense")
        if record.get("legacy_id") and record["id"] in allowed:
            warnings.append(message + " (allowlisted in docs/notes/label-cleanup.json)")
        else:
            errors.append(message)
    return errors, warnings


def validate_identity(root: Path) -> None:
    errors, _ = _scan(root)
    if errors:
        raise IdentityError(errors[0] if len(errors) == 1 else f"{errors[0]} (and {len(errors) - 1} more identity errors)")


def identity_warnings(root: Path) -> list[str]:
    from label_cleanup import CLEANUP as LIST, passing

    warnings = _scan(root)[1]
    warnings.extend(f"{entry['kind']} {entry['id']}: label clean-up entry passes ({reason}); remove it from {LIST}"
                    for entry, reason in passing(root))
    return warnings
