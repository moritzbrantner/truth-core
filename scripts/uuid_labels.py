"""Derive the display label of a migrated record (owner rules, 2026-11-07).

A label names the thing plainly: a statement by its proposition in short form,
an argument or result by its conclusion and route, a definition by its term
and sense. Labels come from the record's prose (paraphrase, meaning, term,
summary, description), not from the old id, are at most LABEL_MAX characters,
contain no id-like text, carry sense tags (`PRIOR_1`) where the record links
exactly one disambiguated sense of the term, and are unique within a kind.

Every compromise is recorded as a cleanup flag (see docs/notes/label-cleanup.md):
`truncated`, `duplicate` (numbered to stay unique), `ids-replaced` (id tokens
in the prose were replaced by words), `from-legacy-id` (part of the label could
only come from the old id), `fallback` (no prose to derive from) and
`untagged-sense` (a linked-sense term whose sense could not be determined).
"""

from __future__ import annotations

import re
from typing import Any

from corpus_ids import IDLIKE_RE, LABEL_MAX, SenseIndex, label_from_legacy, sense_head

LEAD_RE = re.compile(
    r"^(?:(?:OPEN|CLOSED|Open|Stated|STATED|Bare|BARE|Conditional|CONDITIONAL)\b[^:]{0,60}:\s*)",
)
SENTENCE_END_RE = re.compile(r"(?<=[a-z0-9\)\]’'\"])[.;]\s+(?=[A-Z(‘'\"“])")


def strip_parentheticals(text: str) -> str:
    out, depth = [], 0
    for ch in text:
        if ch in "([":
            depth += 1
            continue
        if ch in ")]" and depth:
            depth -= 1
            continue
        if depth == 0:
            out.append(ch)
    return "".join(out)


def clean(text: str, flags: set[str]) -> str:
    text = text.replace("`", "").replace("\n", " ")
    text = LEAD_RE.sub("", text.strip())
    shorter = strip_parentheticals(text)
    if shorter.strip():
        text = shorter

    def words(match: re.Match[str]) -> str:
        flags.add("ids-replaced")
        return label_from_legacy(match.group(0))

    text = IDLIKE_RE.sub(words, text)
    text = re.sub(r"\s+([,.;:])", r"\1", re.sub(r"\s+", " ", text)).strip(" ,;:")
    return text


def first_sentence(text: str) -> str:
    return SENTENCE_END_RE.split(text, maxsplit=1)[0].rstrip(".;: ")


def shorten(text: str, limit: int, flags: set[str]) -> str:
    if len(text) <= limit:
        return text
    flags.add("truncated")
    cut = text[: limit - 1]
    if " " in cut:
        cut = cut[: cut.rindex(" ")]
    return cut.rstrip(" ,;:-") + "…"


def capitalize(text: str) -> str:
    return text[:1].upper() + text[1:] if text else text


def phrase(text: Any, flags: set[str], limit: int = LABEL_MAX) -> str:
    if not isinstance(text, str) or not text.strip():
        return ""
    return shorten(capitalize(first_sentence(clean(text, flags))), limit, flags)


def tag_senses(label: str, kind: str, record: dict[str, Any], senses: SenseIndex, flags: set[str]) -> str:
    linked = senses.linked_senses(kind, record)
    by_head: dict[str, set[str]] = {}
    for head, tag, _ in linked:
        by_head.setdefault(head, set()).add(tag)
    for head in sorted(by_head, key=len, reverse=True):
        tags = by_head[head]
        pattern = re.compile(r"(?<![\w])" + re.escape(head) + r"(?![\w])", re.IGNORECASE)
        if not pattern.search(label):
            continue
        if len(tags) == 1:
            label = pattern.sub(next(iter(tags)), label)
        else:
            flags.add("untagged-sense")
    return label


def route_of(legacy: str, conclusion_label: str, flags: set[str]) -> str:
    match = re.search(r"(?:^|-)(FROM|VIA|BY)-(.+)$", legacy)
    if match:
        flags.add("from-legacy-id")
        return f"{match.group(1).lower()} {label_from_legacy(match.group(2))}"
    return ""


class Labeler:
    def __init__(self, records: dict[str, dict[str, dict[str, Any]]], senses: SenseIndex) -> None:
        self.records = records  # kind -> id -> record (ids already uuids)
        self.senses = senses
        self.flags: dict[tuple[str, str], set[str]] = {}

    def label_of(self, kind: str, record_id: str) -> str:
        record = self.records.get(kind, {}).get(record_id)
        if record is None:
            return label_from_legacy(record_id)
        return record.get("label") or label_from_legacy(record.get("legacy_id", record_id))

    def base(self, kind: str, record: dict[str, Any], flags: set[str]) -> str:
        legacy = record.get("legacy_id") or record["id"]
        if kind == "statement":
            text = phrase(record.get("paraphrase"), flags)
        elif kind == "argument" or kind == "result":
            argument = record if kind == "argument" else self.records["argument"].get(record.get("argument_id"), {})
            if kind == "result" and argument.get("label"):
                return argument["label"]
            conclusion = self.label_of("statement", argument.get("conclusion_statement_id", ""))
            route = route_of(argument.get("legacy_id", legacy), conclusion, flags)
            if not route:
                premises = argument.get("premise_statement_ids", [])
                if premises:
                    first = self.label_of("statement", premises[0])
                    more = f" and {len(premises) - 1} more" if len(premises) > 1 else ""
                    route = f"from {shorten(first, 45, set())}{more}"
            text = shorten(conclusion, LABEL_MAX - len(route) - 2, flags) + ", " + route if route else conclusion
        elif kind == "inference":
            output = self.label_of("statement", record.get("output_statement_id", ""))
            rule = phrase(str(record.get("rule", "")).replace("_", " "), flags, 30)
            text = shorten(output, LABEL_MAX - len(rule) - 5, flags) + (f", by {rule}" if rule else "")
        elif kind == "definition":
            term = phrase(record.get("term"), flags, 40)
            gist = phrase(record.get("definition"), flags, LABEL_MAX - len(term) - 2)
            text = f"{term}: {gist}" if gist else term
        elif kind == "disambiguation":
            text = phrase(record.get("term"), flags)
        elif kind == "claim":
            source = self.label_of("source", record.get("source_id", ""))
            locator = phrase(re.split(r"[:\"“]", str(record.get("locator", "")))[0], flags, 30)
            statement = self.label_of("statement", record.get("statement_id", ""))
            head = shorten(f"{source} {locator}".strip(), 45, flags)
            text = shorten(f"{head}: {statement}", LABEL_MAX, flags)
        elif kind == "source":
            author = phrase(record.get("author"), flags, 40)
            work = phrase(re.split(r"[,:]", str(record.get("work", "")))[0], flags, LABEL_MAX - len(author) - 2)
            text = f"{author}, {work}" if author and work else (author or work)
        elif kind == "passage":
            source = self.label_of("source", record.get("source_id", ""))
            locator = phrase(record.get("locator"), flags, 60)
            text = shorten(f"{source}, {locator}", LABEL_MAX, flags)
        elif kind == "relation":
            subject = self.label_of(record.get("subject_kind", ""), record.get("subject_id", ""))
            obj = self.label_of(record.get("object_kind", ""), record.get("object_id", ""))
            predicate = str(record.get("predicate", "")).replace("_", " ")
            room = (LABEL_MAX - len(predicate) - 2) // 2
            text = f"{shorten(subject, room, flags)} {predicate} {shorten(obj, room, flags)}"
        elif kind == "candidate":
            text = phrase(record.get("goal"), flags)
        elif kind == "attempt":
            text = phrase(record.get("summary"), flags)
        else:  # model, configuration
            text = phrase(record.get("description"), flags)
        if not text:
            flags.add("fallback")
            flags.add("from-legacy-id")
            text = capitalize(label_from_legacy(legacy))
        return text

    def make(self, kind: str, record: dict[str, Any]) -> str:
        flags: set[str] = set()
        text = self.base(kind, record, flags)
        text = tag_senses(text, kind, record, self.senses, flags)
        if IDLIKE_RE.search(text):
            flags.add("ids-replaced")
            text = IDLIKE_RE.sub(lambda m: label_from_legacy(m.group(0)), text)
        text = shorten(text, LABEL_MAX, flags)
        if self.senses.untagged(kind, text, record):
            flags.add("untagged-sense")
        self.flags[(kind, record["id"])] = flags
        return text


def make_unique(labels: dict[str, str], fixed: set[str], flags: dict[str, set[str]]) -> dict[str, str]:
    """Number duplicate labels within one kind; labels in `fixed` keep their text."""
    taken: dict[str, int] = {}
    for record_id in sorted(fixed):
        taken[labels[record_id].casefold()] = 1
    out = dict(labels)
    for record_id in sorted(set(labels) - fixed, key=lambda key: (labels[key], key)):
        label = labels[record_id]
        key = label.casefold()
        if key not in taken:
            taken[key] = 1
            continue
        number = taken[key] + 1
        while True:
            suffix = f" ({number})"
            candidate = shorten(label, LABEL_MAX - len(suffix), set()) + suffix
            if candidate.casefold() not in taken:
                break
            number += 1
        taken[key] = number
        taken[candidate.casefold()] = 1
        out[record_id] = candidate
        flags.setdefault(record_id, set()).add("duplicate")
    return out


__all__ = ["Labeler", "make_unique", "sense_head"]
