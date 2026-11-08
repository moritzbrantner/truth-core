#!/usr/bin/env python3
"""Sense-indexed terms: label migration, mixing report and allowlist.

Owner direction (2026-11-07): each disambiguated term carries numbered senses
(PRIOR_1, PRIOR_2, ...) whose identity is an opaque uuid4; one argument uses
one sense per term, and an argument valid in several senses is recorded once
per sense. See docs/corpus-model.md, "Sense-indexed terms".

  migrate [--write]    give every disambiguation a term_label and uuid senses
  report [--write]     list arguments that mix senses of a term without a
                       bridge (docs/notes/sense-index-migration.md)
  allowlist [--write]  regenerate corpus/sense-index-allowlist.json from the
                       current mixing and undeclared senses (legacy entries warn)
  ratchet --base REV   fail if the allowlist gained an entry since REV (#1233);
                       list entries that no longer fail and can be removed
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import unicodedata
import uuid
from pathlib import Path
from typing import Any

import corpus

NOTE = Path("docs") / "notes" / "sense-index-migration.md"


MAX_TERM_WORDS = 6
CONNECTORS = {"AND", "OR", "OF", "THE", "A", "AN", "IN", "TO", "VERSUS", "VS", "FROM", "BY", "AS", "AT", "ON", "FOR"}


def normalize_term(term: str) -> str:
    """`prior (simply, in time, or in substance)` -> PRIOR: parentheticals
    dropped, ASCII-folded, upper snake case."""
    text = re.sub(r"\([^()]*\)", " ", term)
    text = unicodedata.normalize("NFKD", text).encode("ascii", "ignore").decode()
    label = re.sub(r"[^A-Za-z0-9]+", "_", text).strip("_").upper()
    if not label:
        return "TERM"
    return label if label[0].isalpha() else f"T_{label}"


def short_term_labels(terms: list[str]) -> dict[str, str]:
    """A short, unique term label per distinct `term` text.

    A long compound record term keeps its first six words, without trailing
    connectors ("reception of esse versus external cause of esse" ->
    RECEPTION_OF_ESSE_VERSUS_EXTERNAL_CAUSE). Records with the same term text
    share a label; when a cut label would merge two different terms, the
    longer one keeps more words until the labels differ."""
    full = {term: normalize_term(term) for term in terms}

    def trimmed(words: list[str]) -> str:
        while len(words) > 1 and words[-1] in CONNECTORS:
            words = words[:-1]
        return "_".join(words)

    labels: dict[str, str] = {}
    owner: dict[str, str] = {}
    for term in sorted(set(terms), key=lambda t: (len(full[t]), full[t])):
        words = full[term].split("_")
        candidates = [trimmed(words[:n]) for n in range(min(MAX_TERM_WORDS, len(words)), len(words) + 1)]
        choice = next((c for c in candidates if owner.get(c, full[term]) == full[term]), full[term])
        owner[choice] = full[term]
        labels[term] = choice
    return labels


def insert_fields(text: str, fields: dict[str, Any]) -> str:
    """Append top-level fields to a JSON object's text, leaving the rest byte-identical."""
    body = text.rstrip()
    assert body.endswith("}"), "a record is a JSON object"
    rendered = "".join(
        ",\n  " + json.dumps(key) + ": " + json.dumps(value, indent=2, ensure_ascii=False).replace("\n", "\n  ")
        for key, value in fields.items()
    )
    return body[:-1].rstrip() + rendered + "\n}\n"


def replace_senses(text: str, senses: list[dict[str, Any]]) -> str:
    """Rewrite the trailing `senses` field (the migration writes it last)."""
    head, marker, _ = text.rpartition(',\n  "senses": ')
    assert marker, "senses is the record's last field"
    return insert_fields(head + "\n}\n", {"senses": senses})


def migrate(write: bool) -> list[str]:
    """Label every disambiguation without senses and give each sense the Lean
    declaration of its definition when it has one; existing labels, uuids and
    declarations are kept."""
    records = corpus.load_dir("disambiguations")
    declarations = {record["id"]: record["lean_declaration"] for _, record in corpus.load_dir("definitions")
                    if record.get("lean_declaration")}
    assigned: dict[tuple[str, str], dict[str, str]] = {}
    counters: dict[str, int] = {}
    for _, record in records:
        term = record.get("term_label")
        for sense in record.get("senses", []):
            assigned[(term, sense["definition_id"])] = sense
            index = int(sense["label"].rsplit("_", 1)[1])
            counters[term] = max(counters.get(term, 0), index)
    changed = []
    taken = {record["term_label"] for _, record in records if "term_label" in record}
    fresh = short_term_labels([record["term"] for _, record in records if "term_label" not in record])
    if taken & set(fresh.values()):
        raise SystemExit(f"new term labels collide with existing ones: {sorted(taken & set(fresh.values()))}")
    for path, record in sorted(records, key=lambda item: item[1]["id"]):
        if "senses" in record:
            senses = [dict(sense, lean_declaration=declarations[sense["definition_id"]])
                      if "lean_declaration" not in sense and sense["definition_id"] in declarations else sense
                      for sense in record["senses"]]
            if senses != record["senses"]:
                changed.append(record["id"])
                if write:
                    path.write_text(replace_senses(path.read_text(encoding="utf-8"), senses), encoding="utf-8")
            continue
        term = record.get("term_label") or fresh[record["term"]]
        senses = []
        for definition_id in record["sense_definition_ids"]:
            key = (term, definition_id)
            if key not in assigned:
                counters[term] = counters.get(term, 0) + 1
                assigned[key] = {"id": str(uuid.uuid4()), "label": f"{term}_{counters[term]}",
                                 "definition_id": definition_id}
                if definition_id in declarations:
                    assigned[key]["lean_declaration"] = declarations[definition_id]
            senses.append(dict(assigned[key]))
        fields = {"senses": senses} if "term_label" in record else {"term_label": term, "senses": senses}
        changed.append(record["id"])
        if write:
            path.write_text(insert_fields(path.read_text(encoding="utf-8"), fields), encoding="utf-8")
    return changed


def mixing() -> list[dict[str, Any]]:
    statements = corpus.index_by_id(corpus.load_dir("statements"), "statement")
    return corpus.sense_mixing(corpus.load_dir("arguments"), statements, corpus.load_dir("disambiguations"))


def undeclared() -> list[dict[str, Any]]:
    return corpus.senses_without_distinct_declaration(corpus.load_dir("disambiguations"))


def allowlist_data(entries: list[dict[str, Any]], senses: list[dict[str, Any]]) -> dict[str, Any]:
    arguments: dict[str, dict[str, list[str]]] = {}
    for entry in entries:
        arguments.setdefault(entry["argument_id"], {})[entry["term"]] = entry["sense_ids"]
    return {"arguments": dict(sorted(arguments.items())),
            "senses_without_lean_declaration": sorted({sense["id"] for sense in senses})}


def allowlist_entries(data: dict[str, Any]) -> set[tuple[str, ...]]:
    """Flat entries: (argument, term, sense) and (sense,)."""
    flat = {(argument, term, sense) for argument, terms in data.get("arguments", {}).items()
            for term, ids in terms.items() for sense in ids}
    return flat | {(sense,) for sense in data.get("senses_without_lean_declaration", [])}


def ratchet(base: str) -> int:
    """The legacy allowlists may only shrink (#1233): fail on any entry the base
    did not have; suggest removing entries that no longer fail."""
    import subprocess
    shown = subprocess.run(["git", "show", f"{base}:{corpus.SENSE_ALLOWLIST.as_posix()}"], cwd=corpus.ROOT,
                           capture_output=True, text=True, check=False)
    head = corpus.load_sense_allowlist()
    needed = allowlist_entries(allowlist_data(mixing(), undeclared()))
    stale = sorted(allowlist_entries(head) - needed)
    for entry in stale:
        print(f"no longer needed, remove from {corpus.SENSE_ALLOWLIST}: {' / '.join(entry)}")
    if shown.returncode != 0:
        print(f"sense ratchet: {corpus.SENSE_ALLOWLIST} is new at {base}; nothing to compare")
        return 0
    added = sorted(allowlist_entries(head) - allowlist_entries(json.loads(shown.stdout)))
    for entry in added:
        print(f"sense ratchet: entry added to {corpus.SENSE_ALLOWLIST}: {' / '.join(entry)}", file=sys.stderr)
    if added:
        print("sense ratchet: the legacy allowlists may only shrink (#1233); split the argument per sense, "
              "list a sense bridge, or give the sense its own Lean declaration instead", file=sys.stderr)
        return 1
    print(f"sense ratchet: ok ({len(stale)} removable entr{'y' if len(stale) == 1 else 'ies'})")
    return 0


def disambiguations_of() -> list[dict[str, Any]]:
    return [record for _, record in corpus.load_dir("disambiguations")]


def report_text(entries: list[dict[str, Any]], senses: list[dict[str, Any]]) -> str:
    arguments = sorted({entry["argument_id"] for entry in entries})
    disambiguations = corpus.load_dir("disambiguations")
    lines = [
        "# Sense-index migration",
        "",
        "Generated by `python3 scripts/sense_index.py report --write`; do not edit by hand.",
        "",
        "Owner direction (2026-11-07): one argument uses one sense per disambiguated term,",
        "and an argument valid in several senses is recorded once per sense",
        "(docs/corpus-model.md, \"Sense-indexed terms\"). The migration gave each of the",
        f"{len(disambiguations)} disambiguations a `term_label` and uuid senses labelled TERM_n.",
        "",
        f"{len(arguments)} existing arguments use two or more senses of one term without a",
        f"sense bridge ({len(entries)} term uses). They are not rewritten: each is listed in",
        f"`{corpus.SENSE_ALLOWLIST.as_posix()}`, so `corpus.py check` reports them as one",
        "warning. A new argument, or an existing one that starts using a sense not",
        "allowlisted for it, is an error. To clear an entry, split the argument into one",
        "argument per sense, or list the premise relating the senses in `sense_bridges`,",
        "then regenerate the allowlist (`python3 scripts/sense_index.py allowlist --write`).",
        "",
        f"Of these, {len({e['argument_id'] for e in entries if '_' not in e['term']})} arguments mix senses of a single-word",
        f"term ({sum('_' not in e['term'] for e in entries)} uses, e.g. PRIOR, CAUSE, GOD, NECESSARY). The rest mix the senses",
        "of a compound disambiguation whose `term` names several related words (for example",
        "\"potency and mutability\"); there the senses are often different words rather than",
        "rival senses of one word, and splitting the record into one disambiguation per word",
        "may clear the entry without splitting the argument.",
        "",
        f"Senses are distinct Lean types: each sense names its own `lean_declaration`. Of the",
        f"{sum(len(d['senses']) for d in disambiguations_of())} senses, {len({s['id'] for s in senses})} have no distinct Lean declaration (none, or",
        "the same constant as another sense of the record); they are allowlisted in the same file",
        "and are not finished senses. The allowlists may only shrink (#1233):",
        "`python3 scripts/sense_index.py ratchet --base <merge-base>` fails on any added entry.",
        "",
        "| Argument | Term | Senses |",
        "| --- | --- | --- |",
    ]
    for entry in sorted(entries, key=lambda e: (e["argument_id"], e["term"])):
        lines.append(f"| `{entry['argument_id']}` | {entry['term']} | {', '.join(entry['labels'])} |")
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("command", choices=("migrate", "report", "allowlist", "ratchet"))
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--base", help="ratchet: the git revision to compare the allowlist with")
    args = parser.parse_args(argv)
    if args.command == "ratchet":
        if not args.base:
            parser.error("ratchet needs --base")
        return ratchet(args.base)
    if args.command == "migrate":
        changed = migrate(args.write)
        print(f"{'labelled' if args.write else 'would label'} {len(changed)} disambiguation(s)")
        return 0
    entries = mixing()
    if args.command == "allowlist":
        data = allowlist_data(entries, undeclared())
        text = json.dumps(data, indent=2, ensure_ascii=False) + "\n"
        target = corpus.ROOT / corpus.SENSE_ALLOWLIST
        if args.write:
            target.write_text(text, encoding="utf-8")
        elif not target.exists() or target.read_text(encoding="utf-8") != text:
            print(f"{corpus.SENSE_ALLOWLIST} is stale; run with --write", file=sys.stderr)
            return 1
        print(f"{len(data['arguments'])} allowlisted argument(s), "
              f"{len(data['senses_without_lean_declaration'])} allowlisted sense(s) without a distinct Lean declaration")
        return 0
    text = report_text(entries, undeclared())
    if args.write:
        (corpus.ROOT / NOTE).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
