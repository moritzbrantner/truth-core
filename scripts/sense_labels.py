"""Sense labels for display and naming (owner direction 2026-11-07).

Each disambiguation gives its term a `term_label` (PRIOR) and its senses an
opaque uuid identity plus a stable display label TERM_n (PRIOR_1). This module
answers, for any record, which sense label each disambiguated term takes in it,
so a dossier can show "prior [PRIOR_1]" and a record label can carry the tag
("Act is PRIOR_1 to potency"). It is lenient: `corpus.py check` validates the
senses; this only reads them.
"""
from __future__ import annotations

from typing import Any, Iterable


def senses_by_definition(disambiguations: Iterable[dict[str, Any]]) -> dict[str, list[dict[str, str]]]:
    """definition id -> [{id, label, term}] over every disambiguation's senses."""
    index: dict[str, list[dict[str, str]]] = {}
    seen: set[str] = set()
    for disambiguation in disambiguations:
        for sense in disambiguation.get("senses", []):
            if not isinstance(sense, dict) or not all(
                isinstance(sense.get(key), str) for key in ("id", "label", "definition_id")
            ):
                continue  # The corpus validator reports malformed sense records.
            if sense["id"] in seen:
                continue
            seen.add(sense["id"])
            index.setdefault(sense["definition_id"], []).append(
                {"id": sense["id"], "label": sense["label"], "term": disambiguation["term_label"]}
            )
    return index


def record_definitions(
    record: dict[str, Any],
    statements: dict[str, dict[str, Any]],
    arguments: dict[str, dict[str, Any]] | None = None,
) -> list[str]:
    """The definitions whose senses a record uses: its own definition_ids,
    those of the statement a claim reads, of an argument's conclusion, premise
    and commitment statements, and of a result's argument. A definition record
    uses its own sense."""
    definitions = [record["id"]] if "definition" in record and "term" in record else []
    definitions.extend(record.get("definition_ids", []))
    statement = statements.get(record.get("statement_id", ""))
    if statement is not None:
        definitions.extend(statement.get("definition_ids", []))
    argument = (arguments or {}).get(record.get("argument_id", ""))
    if argument is not None:
        definitions.extend(record_definitions(argument, statements))
    if "conclusion_statement_id" in record:
        for sid in (record["conclusion_statement_id"], *record.get("premise_statement_ids", []),
                    *record.get("commitment_statement_ids", [])):
            definitions.extend(statements.get(sid, {}).get("definition_ids", []))
    return definitions


def record_sense_labels(
    record: dict[str, Any],
    statements: dict[str, dict[str, Any]],
    by_definition: dict[str, list[dict[str, str]]],
    arguments: dict[str, dict[str, Any]] | None = None,
) -> dict[str, list[str]]:
    """term_label -> sorted sense labels the record uses (one per term unless it
    mixes senses). An argument's declared `term_senses` count too."""
    labels: dict[str, set[str]] = {}
    for definition_id in record_definitions(record, statements, arguments):
        for sense in by_definition.get(definition_id, []):
            labels.setdefault(sense["term"], set()).add(sense["label"])
    raw = record.get("term_senses", {})
    declared = dict(raw) if isinstance(raw, dict) else {}
    argument = (arguments or {}).get(record.get("argument_id", ""))
    if argument is not None:
        raw = argument.get("term_senses", {})
        if isinstance(raw, dict):
            declared.update(raw)
    by_id = {sense["id"]: sense for senses in by_definition.values() for sense in senses}
    for term, sense_id in declared.items():
        if isinstance(sense_id, str) and sense_id in by_id:
            labels.setdefault(term, set()).add(by_id[sense_id]["label"])
    return {term: sorted(values) for term, values in sorted(labels.items())}


def format_sense_labels(labels: dict[str, list[str]]) -> str:
    """`PRIOR_1, CAUSE_2` (a mixed term shows each of its senses)."""
    return ", ".join(label for values in labels.values() for label in values)


def sense_labels_from_data(data: dict[str, list[dict[str, Any]]]):
    """A `record -> {term: [labels]}` function over loaded corpus lists."""
    statements = {entry["id"]: entry for entry in data.get("statements", [])}
    arguments = {entry["id"]: entry for entry in data.get("arguments", [])}
    by_definition = senses_by_definition(data.get("disambiguations", []))
    return lambda record: record_sense_labels(record, statements, by_definition, arguments)
