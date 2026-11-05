"""Read-only reconciliation of issue acceptance blocks with corpus records (#949).

This module is deliberately a projection: existence/status checks do not run Lean,
Comparator, source verification, or close issues on GitHub.
"""

from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path
from typing import Any


FIELDS = ("results", "theorems", "statements", "configurations", "attempts")
STATUSES = {"closed", "proved", "sourced"}
FENCE = re.compile(r"^```truth-core-acceptance[ \t]*\r?\n(.*?)^```[ \t]*$", re.MULTILINE | re.DOTALL)
FENCE_START = re.compile(r"^```truth-core-acceptance[ \t]*$", re.MULTILINE)
FIELD = re.compile(r"^([a-z_]+):[ \t]*\[(.*)\][ \t]*$")
IDENTIFIER = re.compile(r"[A-Za-z0-9_.-]+\Z")


def read_issue_snapshot(path: Path | None) -> list[dict[str, Any]]:
    """Accept `gh issue list --json ...` output or fetch the equivalent list."""
    if path is None:
        try:
            command = ["gh", "issue", "list", "--state", "open", "--limit", "1000",
                       "--json", "number,title,body,url,comments"]
            result = subprocess.run(command, capture_output=True, text=True, timeout=45, check=False)
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise ValueError(f"cannot list GitHub issues: {exc}; pass --from with an offline JSON snapshot") from exc
        if result.returncode != 0:
            raise ValueError(f"gh issue list failed: {result.stderr.strip()}; pass --from for offline use")
        raw = result.stdout
    else:
        try:
            raw = path.read_text(encoding="utf-8")
        except OSError as exc:
            raise ValueError(f"cannot read {path}: {exc}") from exc
    try:
        items = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise ValueError(f"issue list is not valid JSON: {exc}") from exc
    if not isinstance(items, list) or any(not isinstance(item, dict) for item in items):
        raise ValueError("issue list must be a JSON array of issue objects")
    if path is None and len(items) >= 1000:
        raise ValueError("gh issue list hit its 1000-issue limit; use a complete offline snapshot")
    return items


DECLARATION = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:public|private|protected|noncomputable|nonrec)\s+)*"
    r"(?:theorem|lemma)\s+([^\s:({\[⦃]+)"
)
NAMESPACE = re.compile(r"^\s*namespace\s+([^\s]+)")
# `mutual … end` also consumes an `end`, so it opens an (unnamed) scope too.
SECTION = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:public|private|noncomputable)\s+)*(?:section|mutual)\b")
END = re.compile(r"^\s*end\b")


def declared_theorems(source: str) -> set[str]:
    """Fully qualified names of `theorem`/`lemma` declarations, following `namespace`/`section`/`end`.

    A lexical approximation of Lean's naming (comments stripped); enough to tell
    `TruthCore.Demo.proof` from `TruthCore.Other.proof` or `TruthCore.Demo.proof'`.
    """
    source = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    scopes: list[list[str]] = []
    names: set[str] = set()
    for line in source.splitlines():
        line = line.split("--", 1)[0]
        if match := NAMESPACE.match(line):
            scopes.append(match.group(1).split("."))
        elif SECTION.match(line):
            scopes.append([])
        elif END.match(line):
            if scopes:
                scopes.pop()
        elif match := DECLARATION.match(line):
            declared = match.group(1)
            if declared.startswith("_root_."):
                names.add(declared[len("_root_."):])
            else:
                names.add(".".join([part for scope in scopes for part in scope] + [declared]))
    return names


def acceptance_text(issue: dict[str, Any]) -> tuple[str | None, list[str]]:
    """Find at most one designated acceptance block, in the body or a comment."""
    bodies = [issue.get("body") or ""]
    comments = issue.get("comments") or []
    if not isinstance(comments, list):
        return None, ["comments must be a list"]
    bodies.extend(comment.get("body") or "" for comment in comments if isinstance(comment, dict))
    # GitHub keeps CRLF from some clients; fences must be found (and counted) either way.
    bodies = [body.replace("\r\n", "\n").replace("\r", "\n") for body in bodies]
    matches = [match.group(1) for body in bodies for match in FENCE.finditer(body)]
    marker_count = sum(len(FENCE_START.findall(body)) for body in bodies)
    if marker_count > len(matches):
        return None, ["unterminated or malformed truth-core-acceptance fence"]
    if len(matches) > 1:
        return None, ["multiple truth-core-acceptance blocks; select one canonical block"]
    return (matches[0], []) if matches else (None, [])


def parse_acceptance(text: str) -> tuple[dict[str, list[tuple[str, str | None]]], list[str]]:
    """Parse the documented YAML-like subset, without a dependency or guesses."""
    requirements: dict[str, list[tuple[str, str | None]]] = {}
    errors: list[str] = []
    for line_number, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        match = FIELD.fullmatch(line)
        if not match:
            errors.append(f"line {line_number}: expected `field: [ID, ...]`")
            continue
        field, values = match.groups()
        if field not in FIELDS:
            errors.append(f"line {line_number}: unknown field {field}")
            continue
        if field in requirements:
            errors.append(f"line {line_number}: duplicate field {field}")
            continue
        parsed: list[tuple[str, str | None]] = []
        for value in values.split(","):
            token = value.strip()
            name, separator, status = token.partition(":") if field == "statements" else (token, "", "")
            name, status = name.strip(), status.strip()
            if not IDENTIFIER.fullmatch(name) or (field == "statements" and (not separator or status not in STATUSES)):
                errors.append(f"line {line_number}: invalid {field} requirement {token!r}")
                continue
            parsed.append((name, status if field == "statements" else None))
        if not parsed:
            errors.append(f"line {line_number}: {field} list must not be empty")
        if len(parsed) != len({name for name, _ in parsed}):
            errors.append(f"line {line_number}: duplicate {field} requirement")
        requirements[field] = parsed
    if not requirements:
        errors.append("acceptance block contains no requirements")
    return requirements, errors


def analyze_issues(
    issues: list[dict[str, Any]], records: dict[str, list[dict[str, Any]]],
    closed_statements: dict[str, str], *, root: Path | None = None,
) -> dict[str, Any]:
    """Evaluate only declared acceptance; unknown and malformed never mean done."""
    by_kind = {kind: {entry["id"]: entry for entry in records[kind]}
               for kind in ("results", "statements", "configurations", "attempts")}
    sourced = {claim["statement_id"] for claim in records.get("claims", [])
               if claim.get("statement_id") and claim.get("source_id") and claim.get("locator")}
    theorem_results = {entry.get("theorem"): entry for entry in records["results"]
                       if isinstance(entry.get("theorem"), str)}
    report: list[dict[str, Any]] = []
    reverse: dict[str, set[int]] = {}
    summary = {status: 0 for status in ("delivered", "missing", "malformed", "untracked")}
    for issue in sorted(issues, key=lambda entry: entry.get("number", 0)):
        number = issue.get("number")
        if not isinstance(number, int) or isinstance(number, bool) or number <= 0:
            raise ValueError("issue number must be a positive integer")
        text, errors = acceptance_text(issue)
        requirements: dict[str, list[tuple[str, str | None]]] = {}
        if text is not None:
            requirements, parse_errors = parse_acceptance(text)
            errors.extend(parse_errors)
        checks: list[dict[str, Any]] = []
        if not errors and text is not None:
            for kind in FIELDS:
                for name, wanted in requirements.get(kind, []):
                    found = by_kind.get(kind, {}).get(name)
                    detail = "absent"
                    met = found is not None
                    if kind == "results":
                        detail = found.get("status", "unknown") if found else "absent"
                        met = bool(found and detail == "solution-present")
                    elif kind == "theorems":
                        result = theorem_results.get(name)
                        met = bool(result and result.get("status") == "solution-present")
                        if met and root is not None:
                            module = result.get("solution_module", "")
                            path = root / (str(module).replace(".", "/") + ".lean")
                            if not path.is_file():
                                met = False
                            else:
                                # The registered fully-qualified name and a source declaration
                                # with exactly that name are both required; compilation remains
                                # CI's job.
                                met = name in declared_theorems(path.read_text(encoding="utf-8"))
                        detail = "registered/source-present" if met else "not a present registered solution theorem"
                    elif kind == "statements":
                        status = closed_statements.get(name)
                        if wanted == "closed":
                            met = bool(found and status)
                        elif wanted == "proved":
                            met = bool(found and status == "proved")
                        else:
                            met = bool(found and name in sourced)
                        detail = status or ("sourced" if name in sourced else "open/absent")
                    elif found:
                        detail = found.get("outcome", "present") if kind == "attempts" else "present"
                    checks.append({"kind": kind, "id": name, "expected": wanted, "met": met, "detail": detail})
                    reverse.setdefault(name, set()).add(number)
        status = ("malformed" if errors else "untracked" if text is None else
                  "delivered" if all(item["met"] for item in checks) else "missing")
        summary[status] += 1
        report.append({"number": number, "title": issue.get("title", ""), "url": issue.get("url", ""),
                       "status": status, "requirements": checks, "errors": errors})
    return {"summary": summary, "issues": report,
            "reverse_index": {name: sorted(numbers) for name, numbers in sorted(reverse.items())}}


def issues_for_id(report: dict[str, Any], canonical_id: str) -> list[int]:
    return list(report["reverse_index"].get(canonical_id, []))
