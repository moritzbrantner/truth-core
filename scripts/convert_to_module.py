#!/usr/bin/env python3
"""Convert TruthCore library files to the Lean module system, bottom-up.

Owner decisions in docs/decisions/2026-11-05-01-lean-module-system.md: every converted file
gets a `module` first line, `public import` for each import, and `@[expose] public section`
after the imports and any leading module docstring. Names, `def` unfolding and NanoDa root
lists stay unchanged. Challenges and the generated aggregators stay ordinary files.

    python3 scripts/convert_to_module.py plan [--max-level N] [--json]
    python3 scripts/convert_to_module.py convert [--max-level N | FILE ...]

`plan` lists every library file that is not yet a module, with its topological level (the
longest chain of TruthCore imports below it) and whether it is convertible now. A file is
convertible when every TruthCore file it imports is a module or is converted in the same run,
and no import is a known non-module external file. `convert --max-level N` converts every
convertible file at level N or lower; with explicit files it converts exactly those (still
refusing an unconvertible one).
"""
from __future__ import annotations

import argparse
import functools
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
IMPORT = re.compile(r"^import\s+([A-Za-z_][A-Za-z0-9_.']*)\s*(--.*)?$")
ANY_IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+([A-Za-z_][A-Za-z0-9_.']*)", re.M)
# External modules that are not modules themselves (a module cannot import them).
NON_MODULE_EXTERNAL = frozenset({"Mathlib.Tactic"})
SECTION = "@[expose] public section\n"


class ConversionError(Exception):
    pass


def is_module_text(text: str) -> bool:
    return _strip_comments_head(text).startswith("module")


def _strip_comments_head(text: str) -> str:
    """Skip leading blank lines, `--` comments and non-doc block comments."""
    i = 0
    while True:
        while i < len(text) and text[i].isspace():
            i += 1
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j + 1
        elif text.startswith("/-", i) and not text.startswith(("/--", "/-!"), i):
            j = text.find("-/", i + 2)
            if j < 0:
                return text[i:]
            i = j + 2
        else:
            return text[i:]


def convert_text(text: str) -> str:
    """Return the module form of an ordinary Lean file's text."""
    if is_module_text(text):
        raise ConversionError("already a module")
    lines = text.splitlines(keepends=True)
    i = 0
    leading: list[str] = []
    imports: list[str] = []
    # Leading plain comments and blank lines stay above the `module` line.
    while i < len(lines):
        s = lines[i].strip()
        if not s or (s.startswith("--") and not imports):
            if not imports:
                leading.append(lines[i])
            i += 1
            continue
        m = IMPORT.match(lines[i].rstrip("\n"))
        if m:
            if m.group(2):
                raise ConversionError(f"import with trailing comment on line {i + 1}")
            imports.append(m.group(1))
            i += 1
            continue
        if s.startswith("import ") or s == "prelude" or s.startswith("prelude "):
            raise ConversionError(f"unsupported header line {i + 1}: {s}")
        break
    rest = lines[i:]
    for n, line in enumerate(rest):
        if line.startswith("import ") or line.startswith("public import "):
            raise ConversionError(f"import after the header on line {i + n + 1}")
    j = 0
    if rest and rest[0].lstrip().startswith("/-!"):
        while j < len(rest) and not rest[j].rstrip().endswith("-/"):
            j += 1
        if j == len(rest):
            raise ConversionError("unterminated leading module docstring")
        j += 1
    head = "".join(leading).lstrip("\n") + "module\n\n"
    if imports:
        head += "".join(f"public import {name}\n" for name in imports) + "\n"
    doc = "".join(rest[:j])
    body = "".join(rest[j:]).lstrip("\n")
    return head + (doc + "\n" if doc else "") + SECTION + "\n" + body


def module_name(path: Path, root: Path) -> str:
    return ".".join(path.relative_to(root).with_suffix("").parts)


def excluded(name: str) -> bool:
    """Challenges and generated aggregators stay ordinary (non-module) files."""
    return name == "TruthCore" or name.endswith(".Challenge") or name.startswith("TruthCore.Imports.")


class Graph:
    def __init__(self, root: Path = ROOT):
        self.root = root
        self.files: dict[str, Path] = {}
        self.imports: dict[str, list[str]] = {}
        self.module: dict[str, bool] = {}
        paths = [root / "TruthCore.lean", *sorted((root / "TruthCore").rglob("*.lean"))]
        for path in paths:
            if not path.exists():
                continue
            name = module_name(path, root)
            text = path.read_text(encoding="utf-8")
            self.files[name] = path
            self.imports[name] = ANY_IMPORT.findall(text)
            self.module[name] = is_module_text(text)

    def local(self, name: str) -> list[str]:
        return [i for i in self.imports[name] if i in self.files]

    @functools.lru_cache(maxsize=None)
    def level(self, name: str) -> int:
        return 1 + max((self.level(i) for i in self.local(name)), default=-1)

    def blocker(self, name: str, selected: set[str]) -> str | None:
        """Why `name` cannot become a module in a run converting `selected`, or None."""
        if excluded(name):
            return "excluded (Challenge or aggregator)"
        for i in self.imports[name]:
            if i in NON_MODULE_EXTERNAL:
                return f"imports non-module {i}"
            if i in self.files and not self.module[i] and i not in selected:
                return f"imports non-module {i}"
        return None

    def candidates(self, max_level: int | None) -> list[str]:
        names = [n for n in self.files if not self.module[n] and not excluded(n)
                 and (max_level is None or self.level(n) <= max_level)]
        return sorted(names, key=lambda n: (self.level(n), n))

    def select(self, max_level: int | None) -> tuple[list[str], dict[str, str]]:
        """Convertible files up to `max_level`, closed under the import requirement."""
        selected = set(self.candidates(max_level))
        blocked: dict[str, str] = {}
        changed = True
        while changed:
            changed = False
            for name in sorted(selected):
                why = self.blocker(name, selected)
                if why:
                    selected.discard(name)
                    blocked[name] = why
                    changed = True
        return sorted(selected, key=lambda n: (self.level(n), n)), blocked


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    plan = sub.add_parser("plan")
    plan.add_argument("--max-level", type=int)
    plan.add_argument("--json", action="store_true")
    conv = sub.add_parser("convert")
    conv.add_argument("--max-level", type=int)
    conv.add_argument("files", nargs="*", type=Path)
    args = parser.parse_args(argv)
    graph = Graph()
    if args.command == "plan":
        selected, blocked = graph.select(args.max_level)
        if args.json:
            print(json.dumps({"convertible": selected, "blocked": blocked}, indent=2))
        else:
            for name in selected:
                print(f"{graph.level(name):3d} {name}")
            for name, why in sorted(blocked.items()):
                print(f"  blocked {name}: {why}")
            print(f"{len(selected)} convertible, {len(blocked)} blocked", file=sys.stderr)
        return 0
    if args.files and args.max_level is not None:
        parser.error("give either --max-level or files")
    if args.files:
        names = [module_name(p.resolve(), graph.root) for p in args.files]
        for name in names:
            if name not in graph.files:
                parser.error(f"not a TruthCore file: {name}")
            why = graph.blocker(name, set(names))
            if why or graph.module[name]:
                print(f"refusing {name}: {why or 'already a module'}", file=sys.stderr)
                return 1
    else:
        names, _ = graph.select(args.max_level)
    try:
        for name in names:
            path = graph.files[name]
            path.write_text(convert_text(path.read_text(encoding="utf-8")), encoding="utf-8")
    except ConversionError as error:
        print(f"{name}: {error}", file=sys.stderr)
        return 1
    print(f"converted {len(names)} files", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
