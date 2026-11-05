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
judgment, and review still checks it. It reads materialized passage text from
the source cache; `--materialize` fetches what is missing.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import source_evidence as se

ROOT = Path(__file__).resolve().parent.parent
ATTRIBUTION_PREFIX = "The passage states "
MIN_ATTRIBUTION_CHARS = 40
# Fields whose change alters what a claim attributes to its source.
ATTRIBUTED_FIELDS = ("statement_id", "source_id", "locator", "interpretation")
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


def changed_paths(base: str, head: str | None) -> list[str]:
    if head is not None:
        return [p for p in git("diff", "--name-only", "-z", "--no-renames", base, head, "--").split("\0") if p]
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
    return json.loads(text)


def changed_claims(base: str, head: str | None) -> list[tuple[dict[str, Any], str]]:
    """Claims the change adds or alters, or whose statement text changed, with a reason."""
    paths = changed_paths(base, head)
    selected: dict[str, tuple[dict[str, Any], str]] = {}
    for path in paths:
        if not (path.startswith("corpus/claims/") and path.endswith(".json")):
            continue
        after = read_at(head, path)
        if after is None:
            continue
        before = read_at(base, path)
        if before is None:
            selected[after["id"]] = (after, "new claim")
            continue
        fields = [field for field in ATTRIBUTED_FIELDS if before.get(field) != after.get(field)]
        if fields:
            selected[after["id"]] = (after, "changed " + ", ".join(fields))
    changed_statements = set()
    for path in paths:
        if path.startswith("corpus/statements/") and path.endswith(".json"):
            after, before = read_at(head, path), read_at(base, path)
            if after is not None and before is not None and after.get("paraphrase") != before.get("paraphrase"):
                changed_statements.add(after["id"])
    if changed_statements:
        for claim_path in sorted((ROOT / "corpus" / "claims").glob("*.json")):
            relative = claim_path.relative_to(ROOT).as_posix()
            claim = read_at(head, relative)
            if claim and claim["statement_id"] in changed_statements and claim["id"] not in selected:
                selected[claim["id"]] = (claim, f"statement {claim['statement_id']} paraphrase changed")
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


def passage_text(passage: dict[str, Any], materialize: bool) -> tuple[str | None, str]:
    """The materialized passage text, or None and why it is unavailable."""
    if se.is_bibliographic(passage):
        return None, f"bibliographic span: read {se.bibliographic_citation(passage)} in the edition itself"
    cached = se.CACHE / f"{passage['id']}.txt"
    if not cached.is_file() and materialize:
        try:
            se.materialize(passage["id"], None)
        except se.SourceEvidenceError as exc:
            return None, f"cannot materialize: {exc}"
    if not cached.is_file():
        return None, f"not materialized: run python3 scripts/source_evidence.py materialize {passage['id']}"
    return cached.read_text(encoding="utf-8"), str(cached.relative_to(ROOT))


def clip(text: str, limit: int) -> str:
    if limit <= 0 or len(text) <= limit:
        return text
    half = limit // 2
    return f"{text[:half]}\n[... {len(text) - limit} characters omitted; read the whole file ...]\n{text[-half:]}"


def report(base: str, head: str | None, *, materialize: bool, max_chars: int) -> tuple[str, list[str]]:
    """Text report and the list of problems that fail the gate."""
    statements = {record["id"]: record for _, record in se.load_json_dir("statements")}
    passages = se.passage_index()
    lines: list[str] = []
    problems: list[str] = []
    claims = changed_claims(base, head)
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
        text, where = passage_text(passage, materialize)
        lines.append("")
        lines.append(f"== {claim['id']} ({reason}) -> {claim['statement_id']}")
        lines.append(f"premise: {statement.get('paraphrase', '(unknown statement)')}")
        lines.append(f"claim locator: {claim['locator']}")
        lines.append(f"claim interpretation: {claim['interpretation']}")
        lines.append(f"passage: {passage['id']} ({passage.get('kind') or 'text_witness'}), {passage['locator']}")
        if text is None:
            lines.append(f"passage text: UNAVAILABLE ({where})")
            if not se.is_bibliographic(passage):
                problems.append(f"{claim['id']}: passage {passage['id']} text not read ({where})")
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
    parser.add_argument("--base", required=True, help="diff base, for example origin/main or the merge base")
    parser.add_argument("--head", help="diff head (default: the working tree, including untracked files)")
    parser.add_argument("--materialize", action="store_true", help="materialize passages not yet in the cache")
    parser.add_argument("--max-chars", type=int, default=6000, help="clip each passage text (0: never)")
    args = parser.parse_args(argv)
    try:
        text, problems = report(args.base, args.head, materialize=args.materialize, max_chars=args.max_chars)
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
