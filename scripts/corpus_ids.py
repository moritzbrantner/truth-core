"""Opaque corpus identity: UUIDs, legacy aliases and display labels (owner decision 2026-11-07).

Every corpus record is identified by an opaque UUID. Readable identifiers such
as ``STMT-NOTHING-PRIOR-TO-ITSELF`` put words, and therefore senses, into
identity; they survive only as ``legacy_id`` aliases (never changed, never
minted again) and as the display-only ``label``.

* A migrated record's id is ``uuid5(NAMESPACE, "<kind>:<legacy_id>")``, so any
  branch converts deterministically by rerunning ``scripts/migrate_uuid.py``.
* A new record's id is ``uuid4`` (``scripts/new_id.py``).
* Input accepts a uuid, a legacy id or a label (``Aliases.resolve``); text
  output prints ``label [uuid8]`` (``Aliases.show``); JSON keeps full uuids.

``REFERENCE_FIELDS`` is the one list of record fields that hold corpus ids,
shared by the migration, its isomorphism check and the alias-aware tools.
"""

from __future__ import annotations

import json
import re
import uuid
from pathlib import Path
from typing import Any, Callable, Iterable, Iterator

# Fixed for the lifetime of the corpus: changing it would re-identify every record.
NAMESPACE = uuid.UUID("d140b0b2-f5a2-4598-9bf7-f3380fb20491")

# Corpus directory -> record kind (the string hashed into the uuid5 name).
KIND_DIRS: dict[str, str] = {
    "sources": "source",
    "statements": "statement",
    "claims": "claim",
    "inferences": "inference",
    "arguments": "argument",
    "relations": "relation",
    "candidates": "candidate",
    "results": "result",
    "definitions": "definition",
    "disambiguations": "disambiguation",
    "attempts": "attempt",
    "models": "model",
    "configurations": "configuration",
    "passages": "passage",
}
DIR_OF_KIND = {kind: directory for directory, kind in KIND_DIRS.items()}

UUID_RE = re.compile(r"^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$")

# Readable prefixes stripped from a legacy id to make its default label.
LABEL_PREFIXES = ("STMT-", "DEF-", "DISAMB-", "INF-", "REL-", "ATTEMPT-", "CONFIG-", "MODEL-")


def is_uuid(value: Any) -> bool:
    return isinstance(value, str) and bool(UUID_RE.match(value))


def legacy_uuid(kind: str, legacy_id: str) -> str:
    """The deterministic id of the record of `kind` whose legacy id is `legacy_id`."""
    if kind not in DIR_OF_KIND:
        raise ValueError(f"unknown corpus kind {kind!r}")
    return str(uuid.uuid5(NAMESPACE, f"{kind}:{legacy_id}"))


def new_uuid() -> str:
    return str(uuid.uuid4())


def label_from_legacy(legacy_id: str) -> str:
    """Display label for a legacy id: prefix dropped, words lower-cased."""
    text = legacy_id
    for prefix in LABEL_PREFIXES:
        if text.startswith(prefix):
            text = text[len(prefix):]
            break
    return text.replace("-", " ").lower()


def order_key(record_id: str, record: dict[str, Any] | None = None) -> str:
    """Tie-break key for deterministic choices: the legacy id when there is one, else the id.

    Choices that used to break ties by readable id (cheapest route, derivation
    order, truncated candidate lists) keep doing so for migrated records, so
    the migration changed no computed result; new records order by uuid."""
    if record is not None and isinstance(record.get("legacy_id"), str):
        return record["legacy_id"]
    return record_id


def short(record_id: str) -> str:
    return record_id[:8] if is_uuid(record_id) else record_id


# ---------------------------------------------------------------------------
# Reference fields.
#
# A path is a tuple of keys; "[]" steps into every list element and "{}" into
# every dict value. A target is a kind, a tuple of kinds tried in order (the
# first kind with a record of that legacy id wins), or "@<key>" for the kind
# named by a sibling key (relations' subject_kind/object_kind).
# ---------------------------------------------------------------------------
TERM_LINKS = ((("definition_ids", "[]"), "definition"), (("disambiguation_ids", "[]"), "disambiguation"))

REFERENCE_FIELDS: dict[str, tuple[tuple[tuple[str, ...], Any], ...]] = {
    "source": (),
    "statement": (
        *TERM_LINKS,
        (("self_evident", "denial_statement_id"), "statement"),
        (("self_evident", "question_statement_id"), "statement"),
        (("self_evident", "disagreement", "claim_ids", "[]"), "claim"),
        (("self_evident", "disagreement", "rival_statement_ids", "[]"), "statement"),
        (("self_evident", "justification_ids", "[]"), ("result", "claim", "argument")),
        (("self_evident", "positions", "[]", "claim_ids", "[]"), "claim"),
        (("self_evident", "positions", "[]", "statement_id"), "statement"),
        (("self_evident", "sceptical_rival_ids", "[]"), "statement"),
    ),
    "claim": (
        *TERM_LINKS,
        (("statement_id",), "statement"),
        (("source_id",), "source"),
        (("interpretation_of",), "claim"),
    ),
    "inference": (
        *TERM_LINKS,
        (("input_statement_ids", "[]"), "statement"),
        (("assumption_statement_ids", "[]"), "statement"),
        (("discharged_statement_ids", "[]"), "statement"),
        (("output_statement_id",), "statement"),
    ),
    "argument": (
        *TERM_LINKS,
        (("premise_statement_ids", "[]"), "statement"),
        (("commitment_statement_ids", "[]"), "statement"),
        (("conclusion_statement_id",), "statement"),
        (("inference_ids", "[]"), "inference"),
        # Sense-indexed terms (feat/sense-indexed-terms): converted if present.
        (("term_senses", "[]", "disambiguation_id"), "disambiguation"),
        (("term_senses", "[]", "definition_id"), "definition"),
        (("term_senses", "[]", "statement_id"), "statement"),
        (("term_senses", "{}", "disambiguation_id"), "disambiguation"),
        (("term_senses", "{}", "definition_id"), "definition"),
        # `term_senses` values and sense-bridge ends are sense uuids, not records.
        (("sense_bridges", "[]", "statement_id"), "statement"),
    ),
    "relation": (
        (("subject_id",), "@subject_kind"),
        (("object_id",), "@object_kind"),
        (("basis",), ("argument", "result")),
        (("background_statement_ids", "[]"), "statement"),
        (("delta_statement_id",), "statement"),
        (("remainder_statement_id",), "statement"),
        (("evidence_result_ids", "{}"), "result"),
        (("explanatory_control_result_ids", "[]"), "result"),
        (("separator", "result_id"), "result"),
        (("strictness_result_id",), "result"),
        (("verification_result_id",), "result"),
    ),
    "candidate": ((("source_id",), "source"),),
    "result": (
        *TERM_LINKS,
        (("argument_id",), "argument"),
        (("case_split", "cases", "[]", "statement_id"), "statement"),
        (("case_split", "survival_result_id"), "result"),
        (("case_split", "target_statement_id"), "statement"),
    ),
    "definition": ((("claim_ids", "[]"), "claim"),),
    "disambiguation": (
        (("sense_definition_ids", "[]"), "definition"),
        (("senses", "[]", "definition_id"), "definition"),
        (("coverage_statement_id",), "statement"),
        (("exclusivity_statement_id",), "statement"),
        (("fork_result_ids", "[]"), "result"),
    ),
    "attempt": (
        (("statement_ids", "[]"), "statement"),
        (("evidence", "[]"), ("result", "claim", "argument")),
    ),
    "model": ((("evaluations", "[]", "statement_id"), "statement"),),
    "configuration": (
        (("seed_statement_id",), "statement"),
        (("configurations", "[]", "statement_ids", "[]"), "statement"),
        (("implication_result_ids", "[]"), "result"),
        (("incompatibility_result_ids", "[]"), "result"),
        (("model_bindings", "[]", "model_id"), "model"),
    ),
    "passage": (),
}

# Dicts whose keys are ids: (kind, path to the dict) -> key kind.
REFERENCE_KEYS: dict[str, tuple[tuple[tuple[str, ...], str], ...]] = {
    "argument": ((("strong_version_needed",), "statement"),),
    "configuration": ((("semantics", "applications"), "statement"),),
}


def keyed_dicts(kind: str, record: dict[str, Any]) -> Iterator[tuple[dict[str, Any], str]]:
    """(dict, key kind) for every dict of `record` whose keys are ids."""
    for path, target in REFERENCE_KEYS.get(kind, ()):
        node: Any = record
        for step in path:
            node = node.get(step) if isinstance(node, dict) else None
        if isinstance(node, dict):
            yield node, target


# Passage files hold a snapshot and a list of passages, not one record.
PASSAGE_FILE_FIELDS = ((("snapshot", "source_id"), "source"),)


Slot = tuple[Any, Any]  # (container, key or index)


def _slots(value: Any, path: tuple[str, ...]) -> Iterator[tuple[Any, Any, Any]]:
    """Yield (container, key, parent dict) for every string slot at `path`."""
    def walk(node: Any, rest: tuple[str, ...], parent: Any) -> Iterator[tuple[Any, Any, Any]]:
        step, tail = rest[0], rest[1:]
        if step == "[]":
            if isinstance(node, list):
                for index, item in enumerate(node):
                    if tail:
                        yield from walk(item, tail, parent)
                    elif isinstance(item, str):
                        yield node, index, parent
        elif step == "{}":
            if isinstance(node, dict):
                for key, item in node.items():
                    if tail:
                        yield from walk(item, tail, node)
                    elif isinstance(item, str):
                        yield node, key, node
        elif isinstance(node, dict) and step in node:
            if tail:
                yield from walk(node[step], tail, node)
            elif isinstance(node[step], str):
                yield node, step, node
    yield from walk(value, path, value)


def reference_slots(kind: str, record: dict[str, Any]) -> Iterator[tuple[Any, Any, tuple[str, ...]]]:
    """(container, key, candidate kinds) for every id-valued field of `record`."""
    fields = PASSAGE_FILE_FIELDS if kind == "passage-file" else REFERENCE_FIELDS.get(kind, ())
    for path, target in fields:
        for container, key, parent in _slots(record, path):
            if isinstance(target, str) and target.startswith("@"):
                named = parent.get(target[1:]) if isinstance(parent, dict) else None
                kinds = (named,) if named in DIR_OF_KIND else ()
            elif isinstance(target, tuple):
                kinds = target
            else:
                kinds = (target,)
            if kinds:
                yield container, key, kinds


def references(kind: str, record: dict[str, Any]) -> list[tuple[str, str]]:
    """Every (candidate kinds joined by '|', id) a record refers to."""
    return [("|".join(kinds), container[key]) for container, key, kinds in reference_slots(kind, record)]


# ---------------------------------------------------------------------------
# Loading and aliases.
# ---------------------------------------------------------------------------
def iter_records(root: Path) -> Iterator[tuple[str, Path, dict[str, Any]]]:
    """(kind, file, record) for every corpus record; passages come from their files."""
    corpus = root / "corpus"
    for directory, kind in KIND_DIRS.items():
        for path in sorted((corpus / directory).glob("*.json")):
            data = json.loads(path.read_text(encoding="utf-8"))
            if not isinstance(data, dict):
                continue
            if kind == "passage":
                for passage in data.get("passages", []):
                    if isinstance(passage, dict):
                        yield kind, path, passage
            else:
                yield kind, path, data


class AmbiguousId(LookupError):
    pass


class Aliases:
    """uuid / legacy id / label -> uuid lookup over loaded records."""

    def __init__(self, records: Iterable[tuple[str, dict[str, Any]]] = ()) -> None:
        self.kind_of: dict[str, set[str]] = {}
        self.label_of: dict[str, str] = {}
        self.legacy_of: dict[str, str] = {}
        self.by_legacy: dict[str, list[tuple[str, str]]] = {}
        self.by_label: dict[str, list[tuple[str, str]]] = {}
        for kind, record in records:
            self.add(kind, record)

    @classmethod
    def load(cls, root: Path) -> "Aliases":
        return cls((kind, record) for kind, _, record in iter_records(root))

    def add(self, kind: str, record: dict[str, Any]) -> None:
        record_id = record.get("id")
        if not isinstance(record_id, str):
            return
        self.kind_of.setdefault(record_id, set()).add(kind)
        legacy = record.get("legacy_id")
        label = record.get("label")
        if isinstance(legacy, str) and legacy:
            self.legacy_of[record_id] = legacy
            self.by_legacy.setdefault(legacy, []).append((kind, record_id))
        if isinstance(label, str) and label:
            self.label_of[record_id] = label
            self.by_label.setdefault(label, []).append((kind, record_id))

    def known(self, value: str) -> bool:
        return value in self.kind_of or value in self.by_legacy

    def candidates(self, token: str, kinds: Iterable[str] | None = None) -> list[tuple[str, str]]:
        wanted = set(kinds) if kinds is not None else None

        def keep(pairs: Iterable[tuple[str, str]]) -> list[tuple[str, str]]:
            return sorted({(k, i) for k, i in pairs if wanted is None or k in wanted})

        if token in self.kind_of:
            found = keep((kind, token) for kind in self.kind_of[token])
            if found:
                return found
        for table in (self.by_legacy, self.by_label):
            found = keep(table.get(token, []))
            if found:
                return found
        folded = token.casefold()
        return keep(pair for label, pairs in self.by_label.items() if label.casefold() == folded for pair in pairs)

    def resolve(self, token: str, kinds: Iterable[str] | None = None) -> str | None:
        """The uuid `token` names (uuid, legacy id or label), None if none.

        Raises AmbiguousId when `token` names more than one record id."""
        found = self.candidates(token, kinds)
        ids = sorted({record_id for _, record_id in found})
        if len(ids) > 1:
            shown = ", ".join(f"{kind} {self.show(record_id)}" for kind, record_id in found)
            raise AmbiguousId(f"{token!r} names several records: {shown}; pass a uuid")
        return ids[0] if ids else None

    def show(self, record_id: str) -> str:
        """Text form: `label [uuid8]`; an unknown or non-uuid id prints as itself."""
        label = self.label_of.get(record_id) or self.legacy_of.get(record_id)
        if label and is_uuid(record_id):
            return f"{label} [{record_id[:8]}]"
        return record_id

    def legacy(self, record_id: str) -> str:
        return self.legacy_of.get(record_id, record_id)


def display_hook(aliases: Aliases) -> Callable[[str], str]:
    return aliases.show


# Prose may cite ids by legacy alias (STMT-…, DEF-…, DISAMB-…) or by uuid.
PROSE_LEGACY_RE = re.compile(r"\b(?:STMT|DEF|DISAMB)-[A-Z0-9]+(?:-[A-Z0-9]+)*\b")
PROSE_UUID_RE = re.compile(r"\b[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\b")


# ---------------------------------------------------------------------------
# Labels (owner rules, 2026-11-07): required, unique within a kind, at most
# LABEL_MAX characters, no uuid-like or id-like text, and every term that has
# a linked sense carries its sense tag (`PRIOR_1`).
# ---------------------------------------------------------------------------
LABEL_MAX = 100
IDLIKE_RE = re.compile(
    r"\b[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)+\b"  # STMT-FOO, Q11-OLD-INTELLECT
    r"|[0-9a-f]{8}-[0-9a-f]{4}"           # uuid-like
)
SENSE_TAG_RE = re.compile(r"\b[A-Z][A-Z0-9_]*_\d+\b")


def idlike_text(label: str) -> list[str]:
    return IDLIKE_RE.findall(label)


def sense_head(term: str) -> str | None:
    """The word(s) a definition's `term` names: text before a parenthesis or colon, at most 3 words."""
    head = re.split(r"\s*[(:;,]", term, maxsplit=1)[0].strip().strip("'\"‘’“”").lower()
    if not head or len(head.split()) > 3 or not re.search(r"[a-z]", head):
        return None
    return head


def sense_tag(head: str, index: int) -> str:
    return re.sub(r"[^A-Z0-9]+", "_", head.upper()).strip("_") + f"_{index}"


class SenseIndex:
    """Which disambiguated sense a record uses for each term, and its tag.

    When disambiguations carry sense records (`senses: [{id, label,
    definition_id}]`, `term_label`; feat/sense-indexed-terms), the tags are
    the sense labels (`PRIOR_1`) that `sense_labels.record_sense_labels` gives
    the record: its own definitions, a claim's statement, an argument's
    premises, conclusion and declared `term_senses`, a result's argument. A
    term the record uses in one sense is tagged; a term it uses in several is
    left untagged and reported. Without sense records, a definition's tag is
    its term's head in upper snake case plus its position among the
    disambiguation's `sense_definition_ids`.
    """

    def __init__(self, definitions: dict[str, dict[str, Any]], disambiguations: dict[str, dict[str, Any]],
                 statements: dict[str, dict[str, Any]] | None = None,
                 arguments: dict[str, dict[str, Any]] | None = None) -> None:
        self.definitions = definitions
        self.disambiguations = disambiguations
        self.statements = statements or {}
        self.arguments = arguments or {}
        self.senses_of: dict[str, list[tuple[str, int]]] = {}
        ordered = sorted(disambiguations, key=lambda key: disambiguations[key].get("legacy_id") or key)
        self.labelled = any(isinstance(disambiguations[key].get("senses"), list)
                            and disambiguations[key].get("term_label") for key in ordered)
        if self.labelled:
            from sense_labels import senses_by_definition

            self.by_definition = senses_by_definition(
                disambiguations[key] for key in ordered
                if isinstance(disambiguations[key].get("senses"), list) and disambiguations[key].get("term_label"))
            self.definitions_of_label: dict[tuple[str, str], set[str]] = {}
            for definition_id, senses in self.by_definition.items():
                for sense in senses:
                    self.definitions_of_label.setdefault((sense["term"], sense["label"]), set()).add(definition_id)
            return
        for disambiguation_id in ordered:
            ids = disambiguations[disambiguation_id].get("sense_definition_ids", [])
            if len(set(ids)) < 2:
                continue
            for index, definition_id in enumerate(ids, start=1):
                self.senses_of.setdefault(definition_id, []).append((disambiguation_id, index))

    def _heads(self, definition_ids: Iterable[str]) -> set[str]:
        heads = set()
        for definition_id in definition_ids:
            head = sense_head(str(self.definitions.get(definition_id, {}).get("term", "")))
            if head:
                heads.add(head)
        return heads

    def linked_senses(self, kind: str, record: dict[str, Any]) -> list[tuple[str, str | None, str]]:
        """(head, tag or None when the record mixes senses, term) for every disambiguated term it uses."""
        if self.labelled:
            from sense_labels import record_sense_labels

            out = []
            used = record_sense_labels(record, self.statements, self.by_definition, self.arguments)
            for term, labels in used.items():
                for label in labels:
                    for head in self._heads(self.definitions_of_label.get((term, label), ())):
                        out.append((head, label if len(labels) == 1 else None, term))
            return out
        linked = list(record.get("definition_ids", []) or [])
        if kind == "definition":
            linked.append(record.get("id"))
        preferred = set(record.get("disambiguation_ids", []) or [])
        out = []
        for definition_id in linked:
            homes = self.senses_of.get(definition_id)
            definition = self.definitions.get(definition_id)
            if not homes or definition is None:
                continue
            head = sense_head(str(definition.get("term", "")))
            if head is None:
                continue
            home = next((h for h in homes if h[0] in preferred), homes[0])
            out.append((head, sense_tag(head, home[1]), definition_id))
        return out

    def untagged(self, kind: str, label: str, record: dict[str, Any]) -> list[str]:
        """Linked-sense terms that occur in `label` without their sense tag."""
        if kind == "disambiguation":
            return []
        missing = []
        for head, _, _ in self.linked_senses(kind, record):
            if re.search(r"(?<![\w])" + re.escape(head) + r"(?![\w])", label, re.IGNORECASE):
                missing.append(head)
        return sorted(set(missing))


def as_uuid_record(kind: str, record: dict[str, Any]) -> dict[str, Any]:
    """A pre-migration record as the migration would identify it (no corpus needed).

    Used to compare records of a revision from before the uuid migration with
    the working tree: the id and every single-kind reference become their
    uuid5 (a multi-kind reference takes its first kind). Labels are not
    derived; callers compare everything except `label`."""
    if not isinstance(record, dict) or is_uuid(record.get("id")) or not isinstance(record.get("id"), str):
        return record
    out = json.loads(json.dumps(record))
    out["legacy_id"] = record["id"]
    out["id"] = legacy_uuid(kind, record["id"])
    for container, key, kinds in reference_slots(kind, out):
        if not is_uuid(container[key]):
            container[key] = legacy_uuid(kinds[0], container[key])
    for node, target in keyed_dicts(kind, out):
        renamed = {(key if is_uuid(key) else legacy_uuid(target, key)): value for key, value in node.items()}
        node.clear()
        node.update(renamed)
    return out


def _without_labels(value: Any) -> Any:
    if isinstance(value, dict):
        return {key: _without_labels(item) for key, item in value.items() if key != "label"}
    if isinstance(value, list):
        return [_without_labels(item) for item in value]
    return value


def identity_only_change(directory: str, before: Any, after: Any) -> bool:
    """Whether a corpus file changed only by the uuid migration (ids, references, labels)."""
    kind = KIND_DIRS.get(directory)
    if kind is None or not isinstance(before, dict) or not isinstance(after, dict):
        return False
    if kind == "passage":
        converted = json.loads(json.dumps(before))
        converted["passages"] = [as_uuid_record("passage", p) for p in converted.get("passages", [])]
        snapshot = converted.get("snapshot")
        if isinstance(snapshot, dict) and isinstance(snapshot.get("source_id"), str) and not is_uuid(snapshot["source_id"]):
            snapshot["source_id"] = legacy_uuid("source", snapshot["source_id"])
    else:
        converted = as_uuid_record(kind, before)
    return _without_labels(converted) == _without_labels(after)
