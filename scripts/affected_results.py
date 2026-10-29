#!/usr/bin/env python3
"""Select and shard the Comparator results that CI must verify.

`select` reads the files a change touches and prints the result IDs whose
verification could be affected:

* every result when the change touches the toolchain, Lake files, tooling,
  verifier or workflow, or an input cannot be classified safely;
* otherwise each result whose own records (`results/<ID>/**`,
  `corpus/results/<ID>.json`) changed, or whose Challenge or Solution module,
  or any `TruthCore` module either imports transitively, changed.

Imports outside `TruthCore` (Mathlib, Lean core) only change with
`lake-manifest.json` or `lean-toolchain`, which select everything.

`nanoda-modules` prints the `TruthCore` modules whose declarations the scoped
NanoDa check must cover on a PR: every changed module and every module that
imports one transitively (its reverse dependents), since only their build
output can differ from the base build. A change that selects every result also
asks for the full scoped check. The set depends only on the two revisions, not
on any cache state.

`external-imports` prints the non-`TruthCore` modules the library imports; CI
keys its once-per-pin full NanoDa check on them.

`select` also emits the heavyweight impact decisions to GITHUB_OUTPUT and the
Actions summary (#568). Recognized documentation bypasses expensive work;
missing diff bases and nightly/manual requests select full coverage. --main
retains exhaustive verification for formal/corpus edits on main.

`explorer` prints whether a change can affect the corpus explorer's code, so CI
runs the explorer browser jobs only then (#520). Corpus records and Lean modules
are the explorer's data, not its code: a change that only adds propositions and
proofs does not run them.

`shard` splits a result list into balanced shards. Results whose Solution
imports Mathlib (directly or through `TruthCore` modules) dominate the run time
(NanoDa re-checks their Mathlib closure), so they are dealt round-robin first.
"""

from __future__ import annotations

import argparse
import fnmatch
import json
import math
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parent.parent

# A change to any of these can change how every result is built or checked.
FULL_RUN_PATTERNS = (
    # Tooling and its tests are trust-boundary changes, including new scripts.
    "scripts/*",
    ".github/*",
    "lean-toolchain",
    "lakefile.toml",
    "lakefile.lean",
    "lake-manifest.json",
    "verifier/*",
)

# What the explorer build and its browser tests run, apart from corpus data: the app, the
# workspace manifests, the Python it imports or shells out to (scripts/corpus.py and its
# imports, the AREAS text of root_imports.py, the pilot fixture) and the workflows.
# test_affected_results.py checks this list against the explorer's sources.
EXPLORER_INPUT_PATTERNS = (
    "apps/corpus-explorer/*",
    "package.json",
    "bun.lock",
    "turbo.json",
    "scripts/corpus.py",
    "scripts/bundle_audit.py",
    "scripts/expression_contracts.py",
    "scripts/contracts/*.json",
    "docs/notes/classical-attributes-migration.json",
    "scripts/research_index.py",
    "scripts/source_evidence.py",
    "scripts/premise_dossiers.py",
    "scripts/finite_models.py",
    "scripts/configurations.py",
    "scripts/configuration_explorer.py",
    "scripts/proposition_structure.py",
    "scripts/PropositionStructure.lean",
    "scripts/strength_comparisons.py",
    "scripts/CheckStrength.lean",
    "scripts/territory.py",
    "scripts/root_imports.py",
    "scripts/testdata/objective-truth-pilot.json",
    "scripts/testdata/frontier-transcription-closure.json",
    ".github/workflows/*",
    ".github/actions/*",
)

IMPORT_RE = re.compile(r"^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(.+?)\s*(?:--.*)?$")

# Run-time weight used to size the shard count: a Mathlib result costs roughly as much as
# MATHLIB_WEIGHT plain results, and one shard runs about SHARD_CAPACITY weight comfortably.
MATHLIB_WEIGHT = 25
SHARD_CAPACITY = 100
MAX_SHARDS = 4


def input_kind(path: str) -> str:
    """Only recognized non-executable prose may bypass the safety fallback.

    Markdown inside an app, verifier, result or script can be a build/test input;
    it deliberately does not inherit the documentation exemption.
    """
    if path in {"AGENTS.md", "CLAUDE.md", "README.md", "CONTEXT.md"} or (
        path.startswith("docs/") and path.endswith(".md")
    ):
        return "docs"
    if changed_module(path):
        return "lean"
    if path.startswith(("corpus/", "results/")) and path.endswith(".json"):
        return "corpus"
    if explorer_inputs_changed([path]):
        return "explorer"
    return "unknown"


def module_path(root: Path, module: str) -> Path:
    return root / (module.replace(".", "/") + ".lean")


def module_imports(root: Path, module: str) -> list[str]:
    """Return the modules a Lean file imports; a missing file imports nothing."""
    path = module_path(root, module)
    if not path.is_file():
        return []
    imports: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = IMPORT_RE.match(line)
        if match:
            imports.extend(match.group(1).split())
    return imports


class ImportGraph:
    def __init__(self, root: Path):
        self.root = root
        self._imports: dict[str, list[str]] = {}
        self._closure: dict[str, frozenset[str]] = {}

    def imports(self, module: str) -> list[str]:
        if module not in self._imports:
            self._imports[module] = module_imports(self.root, module)
        return self._imports[module]

    def closure(self, module: str) -> frozenset[str]:
        """The module itself and every module it imports transitively (any package)."""
        if module in self._closure:
            return self._closure[module]
        seen: set[str] = set()
        stack = [module]
        while stack:
            current = stack.pop()
            if current in seen:
                continue
            seen.add(current)
            if current.split(".")[0] == "TruthCore":
                stack.extend(self.imports(current))
        result = frozenset(seen)
        self._closure[module] = result
        return result


def load_results(root: Path) -> dict[str, dict]:
    """Map each result ID to its Comparator config."""
    results: dict[str, dict] = {}
    for record_path in sorted((root / "corpus" / "results").glob("*.json")):
        record = json.loads(record_path.read_text(encoding="utf-8"))
        config_path = root / record["comparator_config"]
        results[record["id"]] = json.loads(config_path.read_text(encoding="utf-8"))
    return results


def result_modules(config: dict) -> list[str]:
    return [config["challenge_module"], config["solution_module"]]


def changed_module(path: str) -> str | None:
    if path.endswith(".lean") and (path.startswith("TruthCore/") or path == "TruthCore.lean"):
        return path[: -len(".lean")].replace("/", ".")
    return None


def needs_full_run(changed: Iterable[str]) -> list[str]:
    return sorted(
        path for path in changed
        if input_kind(path) == "unknown"
        or any(fnmatch.fnmatchcase(path, pattern) for pattern in FULL_RUN_PATTERNS)
    )


def impact_plan(root: Path, changed: Iterable[str] | None, *, main: bool = False) -> dict:
    """One exact-diff plan for existing jobs; None means unavailable base or full request.

    Corpus edits retain binding and source work. Explorer unit tests read both
    corpus data and Lean source (site-state.test.ts indexes advertised declarations).
    Browser selection reuses the existing code-input classification. Report production
    remains live for every non-prose input; no absent report certifies a build.
    """
    changed = None if changed is None else sorted(set(changed))
    safety = ["full run requested or exact base unavailable"] if changed is None else needs_full_run(changed)
    kinds = {input_kind(p) for p in changed or []}
    formal = bool(kinds & {"lean", "corpus"})
    full = bool(safety) or (main and formal)
    mode, selected = ("full", sorted(load_results(root))) if full else select(root, changed or [])
    library = full or "lean" in kinds
    lean = full or formal
    source = full or "corpus" in kinds
    browser = bool(safety) or bool(explorer_inputs_changed(changed or []))
    explorer = browser or formal
    report = lean or browser
    reason = ", ".join(safety) if safety else (
        "main formal/corpus change: exhaustive verification" if full else ", ".join(changed or []) or "empty exact diff"
    )
    checks = {"fast": True, "lean": lean, "source": source, "library_changed": library,
              "explorer_tests": explorer, "explorer": browser, "report": report,
              "comparator_library": library or report, "full": full}
    return {"mode": mode, "selected": selected, "checks": checks, "reason": reason}


def select(root: Path, changed: Iterable[str]) -> tuple[str, list[str]]:
    """Return ("full" | "subset", result IDs) for a set of changed repository paths."""
    changed = sorted(set(changed))
    results = load_results(root)
    if needs_full_run(changed):
        return "full", sorted(results)
    changed_modules = {module for module in map(changed_module, changed) if module}
    changed_set = set(changed)
    graph = ImportGraph(root)
    selected = []
    for result_id, config in results.items():
        own = {f"corpus/results/{result_id}.json"}
        record_changed = bool(own & changed_set) or any(
            path.startswith(f"results/{result_id}/") for path in changed
        )
        module_changed = any(graph.closure(module) & changed_modules for module in result_modules(config))
        if record_changed or module_changed:
            selected.append(result_id)
    return "subset", sorted(selected)


def imports_mathlib(graph: ImportGraph, config: dict) -> bool:
    return any(
        module.split(".")[0] == "Mathlib" for name in result_modules(config) for module in graph.closure(name)
    )


def shard_count(root: Path, result_ids: list[str]) -> int:
    if not result_ids:
        return 0
    results = load_results(root)
    graph = ImportGraph(root)
    weight = sum(MATHLIB_WEIGHT if imports_mathlib(graph, results[r]) else 1 for r in result_ids)
    return max(1, min(MAX_SHARDS, math.ceil(weight / SHARD_CAPACITY)))


def shard(root: Path, result_ids: list[str], index: int, count: int) -> list[str]:
    """Deal results round-robin into `count` shards, Mathlib results first, and return one."""
    if count < 1 or not 0 <= index < count:
        raise ValueError(f"shard index {index} out of range for {count} shards")
    results = load_results(root)
    graph = ImportGraph(root)
    ordered = sorted(result_ids, key=lambda r: (not imports_mathlib(graph, results[r]), r))
    return sorted(ordered[index::count])


def external_imports(root: Path, module: str = "TruthCore") -> list[str]:
    """Modules outside `TruthCore` that the library imports, directly or transitively."""
    graph = ImportGraph(root)
    return sorted(m for m in graph.closure(module) if m.split(".")[0] != "TruthCore")


def library_modules(root: Path) -> list[str]:
    """Every TruthCore module present in the tree."""
    modules = [changed_module(path.relative_to(root).as_posix()) for path in (root / "TruthCore").rglob("*.lean")]
    if (root / "TruthCore.lean").is_file():
        modules.append("TruthCore")
    return sorted(module for module in modules if module)


def nanoda_scope(root: Path, changed: Iterable[str]) -> tuple[str, list[str]]:
    """Return ("full" | "scoped", modules): the modules whose declarations NanoDa must check.

    "full" means every TruthCore declaration (the module list is then empty). Otherwise the list
    holds each changed module that still exists and each module that imports a changed module
    (existing or deleted) transitively, sorted. An empty list means no build output changed.
    """
    changed = sorted(set(changed))
    if needs_full_run(changed):
        return "full", []
    changed_modules = {module for module in map(changed_module, changed) if module}
    if not changed_modules:
        return "scoped", []
    graph = ImportGraph(root)
    return "scoped", [m for m in library_modules(root) if graph.closure(m) & changed_modules]


def explorer_inputs_changed(changed: Iterable[str]) -> list[str]:
    return sorted(
        path for path in changed if any(fnmatch.fnmatchcase(path, pattern) for pattern in EXPLORER_INPUT_PATTERNS)
    )


def git_changed_files(root: Path, base: str, head: str) -> list[str]:
    output = subprocess.run(
        ["git", "diff", "--name-only", "-z", "--no-renames", base, head, "--"],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
        timeout=30,
    ).stdout
    return [path for path in output.split("\0") if path]


def changed_files_or_full(root: Path, base: str, head: str) -> list[str] | None:
    try:
        return git_changed_files(root, base, head)
    except (subprocess.SubprocessError, OSError) as exc:
        print(f"cannot resolve exact diff; full verification: {exc}", file=sys.stderr)
        return None


def write_github_output(values: dict[str, str]) -> None:
    target = os.environ.get("GITHUB_OUTPUT")
    if not target:
        return
    with open(target, "a", encoding="utf-8") as handle:
        for key, value in values.items():
            handle.write(f"{key}={value}\n")


def command_select(args: argparse.Namespace) -> int:
    root = Path(args.root)
    if args.all:
        changed = None
    else:
        if args.files_from:
            changed = [line.strip() for line in Path(args.files_from).read_text().splitlines() if line.strip()]
        else:
            changed = changed_files_or_full(root, args.base, args.head)
    plan = impact_plan(root, changed, main=args.main)
    mode, selected = plan["mode"], plan["selected"]
    count = shard_count(root, selected)
    print(f"impact plan: {plan['reason']}", file=sys.stderr)
    print(f"{mode}: {len(selected)} results in {count} shard(s)", file=sys.stderr)
    if args.output:
        Path(args.output).write_text("".join(f"{r}\n" for r in selected), encoding="utf-8")
    else:
        for result_id in selected:
            print(result_id)
    write_github_output(
        {
            "mode": mode,
            "count": str(len(selected)),
            **{key: str(value).lower() for key, value in plan["checks"].items()},
            "shards": json.dumps(list(range(count))),
            "shard_count": str(count),
        }
    )
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a", encoding="utf-8") as handle:
            handle.write("### Exact-head impact plan\n\n")
            handle.write(f"Selection: {mode}, {len(selected)} results. Reason: {plan['reason']}\n\n")
            handle.write("| Check | Decision |\n| --- | --- |\n")
            for key, run in plan["checks"].items():
                handle.write(f"| {key} | {'run' if run else 'unaffected inputs; bypass'} |\n")
            handle.write("\nA bypass is an unaffected-input decision, not fresh formal certification or a report.\n")
    return 0


def command_explorer(args: argparse.Namespace) -> int:
    if args.all:
        changed_inputs = ["full run requested"]
    else:
        changed = changed_files_or_full(Path(args.root), args.base, args.head)
        changed_inputs = (["exact base unavailable"] if changed is None else
                          needs_full_run(changed) or explorer_inputs_changed(changed))
    run = "true" if changed_inputs else "false"
    print(f"explorer inputs changed: {', '.join(changed_inputs) or 'none'}", file=sys.stderr)
    print(run)
    write_github_output({"explorer": run})
    return 0


def command_nanoda_modules(args: argparse.Namespace) -> int:
    root = Path(args.root)
    changed = changed_files_or_full(root, args.base, args.head)
    scope, modules = ("full", []) if changed is None else nanoda_scope(root, changed)
    detail = "every TruthCore declaration" if scope == "full" else f"{len(modules)} affected module(s)"
    print(f"NanoDa scope: {scope}, {detail}", file=sys.stderr)
    text = "".join(f"{module}\n" for module in modules)
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    write_github_output({"scope": scope, "count": str(len(modules))})
    return 0


def command_shard(args: argparse.Namespace) -> int:
    root = Path(args.root)
    if args.results_file:
        ids = [line.strip() for line in Path(args.results_file).read_text().splitlines() if line.strip()]
    else:
        ids = sorted(load_results(root))
    for result_id in shard(root, ids, args.index, args.count):
        print(result_id)
    return 0


def command_external_imports(args: argparse.Namespace) -> int:
    for module in external_imports(Path(args.root)):
        print(module)
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", default=str(ROOT))
    sub = parser.add_subparsers(dest="command", required=True)
    sel = sub.add_parser("select", help="print the results a change can affect")
    source = sel.add_mutually_exclusive_group(required=True)
    source.add_argument("--base", help="git revision to diff against (with --head)")
    source.add_argument("--files-from", help="file listing changed paths, one per line")
    source.add_argument("--all", action="store_true", help="select every result")
    sel.add_argument("--head", default="HEAD")
    sel.add_argument("--main", action="store_true", help="retain exhaustive main verification for formal/corpus changes")
    sel.add_argument("--output", help="write the selected IDs here instead of stdout")
    sel.set_defaults(func=command_select)
    exp = sub.add_parser("explorer", help="print whether a change can affect the explorer's code")
    exp_source = exp.add_mutually_exclusive_group(required=True)
    exp_source.add_argument("--base", help="git revision to diff against (with --head)")
    exp_source.add_argument("--all", action="store_true", help="treat every explorer input as changed")
    exp.add_argument("--head", default="HEAD")
    exp.set_defaults(func=command_explorer)
    nd = sub.add_parser("nanoda-modules", help="print the TruthCore modules a PR's scoped NanoDa check covers")
    nd.add_argument("--base", required=True, help="git revision to diff against")
    nd.add_argument("--head", default="HEAD")
    nd.add_argument("--output", help="write the module names here instead of stdout")
    nd.set_defaults(func=command_nanoda_modules)
    sh = sub.add_parser("shard", help="print one balanced shard of a result list")
    sh.add_argument("--index", type=int, required=True)
    sh.add_argument("--count", type=int, required=True)
    sh.add_argument("--results-file", help="result IDs to shard (default: every result)")
    sh.set_defaults(func=command_shard)
    ext = sub.add_parser(
        "external-imports",
        help="print the non-TruthCore modules the library imports (keys the full NanoDa check)",
    )
    ext.set_defaults(func=command_external_imports)
    args = parser.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
