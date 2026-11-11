#!/usr/bin/env python3
"""Pre-push attribution self-check for stating claims (#989).

The most frequent review P1 in research PRs is source over-attribution: a
claim records a premise as *stated* by a passage that only supports it, or
states something narrower. This gate runs before the first push. For every
claim the change adds or alters (or whose statement text changed) it prints
the premise text next to the claim's locator and the pinned passage text, and
it fails unless the claim records a one-line `attribution` of the form
"The passage states X, which is the premise." A claim that cannot honestly
carry that sentence is downgraded to a `supports` relation with a gap note
(#987), not kept as a stating claim.

The check is mechanical only about presence: the sentence is the worker's
judgment, and review still checks it. The default check is offline: cached text
is shown when available, and missing or stale text is explicitly not checked.
Use `--materialize` for an opt-in passage check that fails on acquisition or
integrity errors; cache availability never establishes that someone read a text.
"""

from __future__ import annotations

import argparse
import contextlib
import io
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import source_evidence as se
from corpus_ids import KIND_DIRS, as_uuid_record, is_uuid, legacy_uuid  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
ATTRIBUTION_PREFIX = "The passage states "
MIN_ATTRIBUTION_CHARS = 40
# Fields whose change alters what a claim attributes to its source.
ATTRIBUTED_FIELDS = ("statement_id", "source_id", "locator", "interpretation", "attribution")
SCOPE_CHECKLIST = (
    "quantifier scope: does the passage say all/every/no where the premise does, or only some/this case?",
    "species/genus: does the passage speak of the whole genus the premise uses (every cause, every being), "
    "or only one species (efficient causes, bodies, motion)?",
    "temporal and modal scope: does the passage assert what the premise asserts about time, beginning, "
    "necessity or possibility, or something narrower?",
)


class AttributionError(Exception):
    pass


def validate_attribution(where: str, claim: dict[str, Any]) -> None:
    """Shape of an optional `attribution` field (checked by `corpus.py check`)."""
    if "attribution" not in claim:
        return
    value = claim["attribution"]
    if (
        not isinstance(value, str)
        or not value.startswith(ATTRIBUTION_PREFIX)
        or len(value.strip()) < MIN_ATTRIBUTION_CHARS
    ):
        raise AttributionError(
            f"{where}: attribution must be one sentence starting {ATTRIBUTION_PREFIX!r} that says what the "
            f"passage states and that it is the premise (at least {MIN_ATTRIBUTION_CHARS} characters)"
        )


def git(*args: str) -> str:
    try:
        return subprocess.run(
            ["git", *args], cwd=ROOT, check=True, capture_output=True, text=True, timeout=60
        ).stdout
    except (subprocess.SubprocessError, OSError) as exc:
        raise AttributionError(f"git {' '.join(args)} failed: {exc}") from exc


def changed_paths(base: str) -> list[str]:
    """Paths changed from `base` to the working tree, including untracked files.
    Renames appear as a deletion and an addition (`--no-renames`)."""
    tracked = git("diff", "--name-only", "-z", "--no-renames", base, "--").split("\0")
    untracked = git("ls-files", "-z", "--others", "--exclude-standard").split("\0")
    return sorted({p for p in [*tracked, *untracked] if p})


def read_at(revision: str | None, path: str) -> dict[str, Any] | None:
    """A JSON record at `revision` (None: the working tree), or None if absent."""
    if revision is None:
        file = ROOT / path
        return json.loads(file.read_text(encoding="utf-8")) if file.is_file() else None
    try:
        text = subprocess.run(
            ["git", "show", f"{revision}:{path}"], cwd=ROOT, check=True, capture_output=True, text=True, timeout=60
        ).stdout
    except subprocess.CalledProcessError:
        return None
    record = json.loads(text)
    # A revision from before the uuid migration is compared under the same ids.
    directory = Path(path).parent.name
    if directory in KIND_DIRS and directory != "passages":
        return as_uuid_record(KIND_DIRS[directory], record)
    if directory == "passages" and isinstance(record, dict):
        record["passages"] = [as_uuid_record("passage", passage) for passage in record.get("passages", [])]
        snapshot = record.get("snapshot")
        if isinstance(snapshot, dict) and isinstance(snapshot.get("source_id"), str) and not is_uuid(snapshot["source_id"]):
            snapshot["source_id"] = legacy_uuid("source", snapshot["source_id"])
    return record


def records_by_id(paths: list[str], directory: str, revision: str | None) -> dict[str, dict[str, Any]]:
    """The records of `directory` among `paths` at `revision`, keyed by stable ID,
    so a moved file is compared with itself rather than treated as new."""
    records = {}
    for path in paths:
        if path.startswith(f"corpus/{directory}/") and path.endswith(".json"):
            record = read_at(revision, path)
            if record is not None and isinstance(record.get("id"), str):
                records[record["id"]] = record
    return records


def changed_passage_ids(paths: list[str], base: str | None = None) -> set[str]:
    """Passages whose manifest the change adds or edits (as in the working tree).

    With `base`, a manifest whose snapshot and passages are unchanged apart from
    identity (uuid ids, labels) changes no passage."""
    changed = set()
    for path in paths:
        if path.startswith("corpus/passages/") and path.endswith(".json"):
            manifest = read_at(None, path)
            if not manifest:
                continue
            if base is not None:
                before = read_at(base, path)
                if before is not None and without_labels(before) == without_labels(manifest):
                    continue
            changed.update(passage["id"] for passage in manifest.get("passages", []) if "id" in passage)
    return changed


def without_labels(value: Any) -> Any:
    if isinstance(value, dict):
        return {key: without_labels(item) for key, item in value.items() if key != "label"}
    if isinstance(value, list):
        return [without_labels(item) for item in value]
    return value


def changed_claims(
    base: str, passages: dict[str, tuple[Path, dict[str, Any]]] | None = None
) -> list[tuple[dict[str, Any], str]]:
    """Claims the change adds or alters, whose statement text changed, or whose
    resolved passage changed, with a reason. The working tree is the head."""
    paths = changed_paths(base)
    before_claims = records_by_id(paths, "claims", base)
    selected: dict[str, tuple[dict[str, Any], str]] = {}
    for claim_id, after in records_by_id(paths, "claims", None).items():
        before = before_claims.get(claim_id)
        if before is None:
            selected[claim_id] = (after, "new claim")
            continue
        fields = [field for field in ATTRIBUTED_FIELDS if before.get(field) != after.get(field)]
        if fields:
            selected[claim_id] = (after, "changed " + ", ".join(fields))
    before_statements = records_by_id(paths, "statements", base)
    changed_statements = {
        statement_id
        for statement_id, after in records_by_id(paths, "statements", None).items()
        if statement_id in before_statements and before_statements[statement_id].get("paraphrase") != after.get("paraphrase")
    }
    changed_passages = changed_passage_ids(paths, base)
    if changed_statements or changed_passages:
        passages = passages if passages is not None else se.passage_index()
        for _, claim in se.load_json_dir("claims"):
            if claim["id"] in selected:
                continue
            if claim["statement_id"] in changed_statements:
                selected[claim["id"]] = (claim, f"statement {claim['statement_id']} paraphrase changed")
                continue
            if changed_passages:
                passage = resolve_passage(claim, passages)
                if passage["id"] in changed_passages:
                    selected[claim["id"]] = (claim, f"passage {passage['id']} changed")
    return [selected[key] for key in sorted(selected)]


def resolve_passage(claim: dict[str, Any], passages: dict[str, tuple[Path, dict[str, Any]]]) -> dict[str, Any]:
    matches = [
        passage
        for _, passage in passages.values()
        if passage["source_id"] == claim["source_id"]
        and any(claim["locator"].startswith(prefix) for prefix in passage["claim_locator_prefixes"])
    ]
    if len(matches) != 1:
        raise AttributionError(f"{claim['id']}: claim resolves to {len(matches)} passages; run source_evidence.py check")
    return matches[0]


def passage_text(passage: dict[str, Any], materialize: bool, changed: bool = False) -> tuple[str | None, str]:
    """The passage text, or None and why it is unavailable. `--materialize`
    always re-materializes (hash-checked against the current manifest); without
    it a cached text is shown only when the change leaves the passage unchanged."""
    if se.is_bibliographic(passage):
        return None, f"bibliographic span: read {se.bibliographic_citation(passage)} in the edition itself"
    cached = se.CACHE / f"{passage['id']}.txt"
    command = f"python3 scripts/source_evidence.py materialize {passage['id']}"
    if materialize:
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                se.materialize(passage["id"], None)
        except se.SourceEvidenceError as exc:
            return None, f"cannot materialize: {exc}"
        return cached.read_text(encoding="utf-8"), f"{cached.relative_to(ROOT)}, materialized now"
    if changed:
        return None, f"the change edits this passage, so a cached text may be stale: run {command} or use --materialize"
    if not cached.is_file():
        return None, f"not materialized: run {command}"
    return cached.read_text(encoding="utf-8"), f"{cached.relative_to(ROOT)}, cached and not re-verified now"


def clip(text: str, limit: int) -> str:
    if limit <= 0 or len(text) <= limit:
        return text
    half = limit // 2
    return f"{text[:half]}\n[... {len(text) - limit} characters omitted; read the whole file ...]\n{text[-half:]}"


def report(base: str, *, materialize: bool, max_chars: int) -> tuple[str, list[str]]:
    """Text report and the list of problems that fail the gate (working tree vs `base`)."""
    statements = {record["id"]: record for _, record in se.load_json_dir("statements")}
    passages = se.passage_index()
    lines: list[str] = []
    problems: list[str] = []
    claims = changed_claims(base, passages)
    edited = changed_passage_ids(changed_paths(base), base) if claims else set()
    if not claims:
        return f"attribution-check: no new or changed stating claim since {base}", []
    lines.append(f"attribution-check: {len(claims)} new or changed stating claim(s) since {base}")
    lines.append("For each claim, compare the premise with what the passage itself says:")
    lines.extend(f"  - {item}" for item in SCOPE_CHECKLIST)
    lines.append(
        f"Then record `attribution`: {ATTRIBUTION_PREFIX}X, which is the premise. If the passage only bears on "
        "the premise or states something narrower, replace the stating claim by a `supports` relation with a gap "
        "note (#987), or state the narrower reading as its own statement."
    )
    for claim, reason in claims:
        statement = statements.get(claim["statement_id"], {})
        passage = resolve_passage(claim, passages)
        text, where = passage_text(passage, materialize, passage["id"] in edited)
        lines.append("")
        lines.append(f"== {claim['id']} ({reason}) -> {claim['statement_id']}")
        lines.append(f"premise: {statement.get('paraphrase', '(unknown statement)')}")
        lines.append(f"claim locator: {claim['locator']}")
        lines.append(f"claim interpretation: {claim['interpretation']}")
        lines.append(f"passage: {passage['id']} ({passage.get('kind') or 'text_witness'}), {passage['locator']}")
        if text is None:
            lines.append(f"passage text: NOT CHECKED in this run ({where})")
            if materialize and not se.is_bibliographic(passage):
                problems.append(f"{claim['id']}: passage {passage['id']} materialization failed ({where})")
        else:
            lines.append(f"passage text ({where}, {len(text)} characters):")
            lines.append(clip(text.rstrip(), max_chars))
        attribution = claim.get("attribution")
        lines.append(f"attribution: {attribution if attribution else 'MISSING'}")
        if not attribution:
            problems.append(f"{claim['id']}: no `attribution` recorded")
        else:
            try:
                validate_attribution(claim["id"], claim)
            except AttributionError as exc:
                problems.append(str(exc))
    return "\n".join(lines), problems


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument(
        "--base", required=True,
        help="diff base, for example origin/main or the merge base; the head is always the working tree",
    )
    parser.add_argument(
        "--materialize", action="store_true",
        help="explicitly materialize selected passages; fail on acquisition or integrity errors",
    )
    parser.add_argument("--max-chars", type=int, default=6000, help="clip each passage text (0: never)")
    args = parser.parse_args(argv)
    try:
        text, problems = report(args.base, materialize=args.materialize, max_chars=args.max_chars)
    except (AttributionError, se.SourceEvidenceError) as exc:
        print(f"attribution-check error: {exc}", file=sys.stderr)
        return 2
    print(text)
    if problems:
        print("\nattribution-check FAILED:", file=sys.stderr)
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
