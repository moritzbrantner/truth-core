#!/usr/bin/env python3
"""Render shared docs tables and lists from one file per entry.

Append-only tables in shared docs (the owner decisions in
`docs/catholic-case.md`, campaign batch tables, candidate lists) are merge
conflict hotspots when parallel lanes each add a row (#416). Each entry lives
in its own Markdown file instead, and this script renders the shared section.
Shared tables are generated, never hand-edited.

A generated section sits between two markers in any Markdown file under
`docs/` or at the repository root:

    <!-- BEGIN GENERATED: docs/decisions table date=Date body=Principle "where=Where recorded" -->
    ...rendered output...
    <!-- END GENERATED -->

The marker arguments are shell-quoted: the entry directory, the format
(`table` or `list`), then for a table one `field=Header` per column, in order.
`filter:field=value` keeps only entries whose field has that value. The field
`body` is the entry's text after its front matter; every other field comes
from the front matter. An entry may omit the body when no column uses it.

An entry is `<dir>/<name>.md`: a front matter block of `key: value` lines
between `---` lines, then the body. Entries render in file-name order, so
name them `<date>-<NN>-<slug>.md` (or another sortable prefix) when order
matters. A table joins the body into one line; a list renders each body as a
`- ` item with its further lines indented by two spaces. A `README.md` in the
entry directory is not an entry.

    python3 scripts/docs_index.py          check (CI); exits 1 and prints a diff if stale
    python3 scripts/docs_index.py --write  regenerate every generated section
"""

from __future__ import annotations

import argparse
import difflib
import re
import shlex
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

BEGIN_RE = re.compile(r"^<!-- BEGIN GENERATED: (?P<spec>.*?) -->$")
END = "<!-- END GENERATED -->"


class DocsIndexError(Exception):
    pass


def parse_entry(path: Path) -> dict[str, str]:
    lines = path.read_text(encoding="utf-8").splitlines()
    if not lines or lines[0] != "---":
        raise DocsIndexError(f"{path}: an entry starts with a '---' front matter line")
    try:
        end = lines.index("---", 1)
    except ValueError:
        raise DocsIndexError(f"{path}: front matter is not closed by a '---' line") from None
    fields: dict[str, str] = {}
    for line in lines[1:end]:
        key, separator, value = line.partition(":")
        if not separator or not key.strip():
            raise DocsIndexError(f"{path}: front matter line is not 'key: value': {line!r}")
        fields[key.strip()] = value.strip()
    body = "\n".join(lines[end + 1 :]).strip("\n")
    if body.strip():
        fields["body"] = body
    return fields


def parse_spec(spec: str, where: str) -> tuple[str, str, list[tuple[str, str]], list[tuple[str, str]]]:
    try:
        tokens = shlex.split(spec)
    except ValueError as exc:
        raise DocsIndexError(f"{where}: cannot parse generated-section marker: {exc}") from None
    if len(tokens) < 2 or tokens[1] not in ("table", "list"):
        raise DocsIndexError(f"{where}: marker needs '<dir> table|list ...', got {spec!r}")
    directory, fmt, rest = tokens[0], tokens[1], tokens[2:]
    columns: list[tuple[str, str]] = []
    filters: list[tuple[str, str]] = []
    for token in rest:
        target = filters if token.startswith("filter:") else columns
        key, separator, value = token.removeprefix("filter:").partition("=")
        if not separator or not key:
            raise DocsIndexError(f"{where}: marker argument is not 'field=value': {token!r}")
        target.append((key, value))
    if fmt == "table" and not columns:
        raise DocsIndexError(f"{where}: a table needs at least one 'field=Header' column")
    if fmt == "list" and columns:
        raise DocsIndexError(f"{where}: a list takes no columns")
    return directory, fmt, columns, filters


def load_entries(root: Path, directory: str, where: str) -> list[tuple[Path, dict[str, str]]]:
    base = root / directory
    if not base.is_dir():
        raise DocsIndexError(f"{where}: entry directory {directory} does not exist")
    return [
        (path, parse_entry(path))
        for path in sorted(base.glob("*.md"))
        if path.name != "README.md"
    ]


def render(root: Path, spec: str, where: str) -> list[str]:
    directory, fmt, columns, filters = parse_spec(spec, where)
    entries = [
        (path, fields)
        for path, fields in load_entries(root, directory, where)
        if all(fields.get(key) == value for key, value in filters)
    ]
    if fmt == "list":
        out: list[str] = []
        for path, fields in entries:
            if "body" not in fields:
                raise DocsIndexError(f"{path.relative_to(root)}: a list entry needs a body ({where})")
            first, *more = fields["body"].splitlines()
            out.append(f"- {first}")
            out.extend(f"  {line}" if line else "" for line in more)
        return out
    out = [
        "| " + " | ".join(header for _, header in columns) + " |",
        "|" + "---|" * len(columns),
    ]
    for path, fields in entries:
        cells = []
        for key, _ in columns:
            if key not in fields:
                raise DocsIndexError(f"{path.relative_to(root)}: missing field {key!r} for {where}")
            cells.append(" ".join(fields[key].split()))
        out.append("| " + " | ".join(cells) + " |")
    return out


def regenerate(root: Path, path: Path) -> str:
    """The file's text with every generated section re-rendered."""
    lines = path.read_text(encoding="utf-8").split("\n")
    out: list[str] = []
    index = 0
    while index < len(lines):
        line = lines[index]
        out.append(line)
        match = BEGIN_RE.match(line)
        index += 1
        if not match:
            continue
        where = f"{path.relative_to(root)}:{index}"
        try:
            end = lines.index(END, index)
        except ValueError:
            raise DocsIndexError(f"{where}: generated section has no '{END}' line") from None
        out.extend(render(root, match.group("spec"), where))
        out.append(END)
        index = end + 1
    return "\n".join(out)


def documents(root: Path) -> list[Path]:
    candidates = sorted((root / "docs").rglob("*.md")) + sorted(root.glob("*.md"))
    return [path for path in candidates if "<!-- BEGIN GENERATED: " in path.read_text(encoding="utf-8")]


def stale(root: Path) -> dict[Path, tuple[str, str]]:
    changed = {}
    for path in documents(root):
        current = path.read_text(encoding="utf-8")
        expected = regenerate(root, path)
        if current != expected:
            changed[path] = (current, expected)
    return changed


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--write", action="store_true", help="regenerate every generated section")
    args = parser.parse_args(argv)
    try:
        changed = stale(ROOT)
    except DocsIndexError as exc:
        print(exc, file=sys.stderr)
        return 1
    if args.write:
        for path, (_, expected) in changed.items():
            path.write_text(expected, encoding="utf-8")
        return 0
    for path, (current, expected) in changed.items():
        name = str(path.relative_to(ROOT))
        sys.stdout.writelines(
            difflib.unified_diff(
                current.splitlines(keepends=True), expected.splitlines(keepends=True), name, name
            )
        )
    if changed:
        print("generated docs sections are stale: run python3 scripts/docs_index.py --write", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
