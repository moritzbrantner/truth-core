#!/usr/bin/env python3
"""PR orphan counts using each revision's shared frontier (no proof rebuild)."""
from __future__ import annotations

import argparse
import io
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile


def orphan_count(reaching, arguments, results, support=(), refuters=()):
    """Same population as truth orphans, including transcriptions."""
    by_id = {argument["id"]: argument for argument in arguments}
    connected_statements = reaching | set(support)
    connected_arguments = set(refuters)
    return sum(
        result.get("status") in ("solution-present", "verified")
        and result["argument_id"] in by_id
        and by_id[result["argument_id"]]["conclusion_statement_id"] not in connected_statements
        and result["argument_id"] not in connected_arguments
        for result in results
    )


def tree_count(tree: Path) -> int:
    # Execute the historical corpus code against its own records: this also
    # avoids mixing legacy and UUID identities across the migration.
    code = """
import json
import corpus
frontier = corpus.current_frontier(corpus.DEFAULT_FRONTIER_ROOT, False, next_steps=False)
if 'reaching_root_statements' not in frontier:
    raise RuntimeError('historical frontier lacks all-route reachability')
reaching = frontier['reaching_root_statements']
arguments = [r for _, r in corpus.load_dir('arguments')]
results = [r for _, r in corpus.load_dir('results')]
support, refuters = (), ()
if hasattr(corpus, 'refutation_support'):
    support, refuters = corpus.refutation_support(
        arguments, results, [r for _, r in corpus.load_dir('relations')], set(reaching))
print(json.dumps([reaching, arguments, results, sorted(support), sorted(refuters)]))
"""
    completed = subprocess.run(
        [sys.executable, "-c", code], cwd=tree / "scripts",
        capture_output=True, text=True, check=True,
    )
    reaching, arguments, results, support, refuters = json.loads(completed.stdout)
    return orphan_count(set(reaching), arguments, results, support, refuters)


def base_count(root: Path, revision: str) -> int:
    archive = subprocess.run(
        ["git", "-C", str(root), "archive", "--format=tar", revision],
        capture_output=True, check=True,
    ).stdout
    with tempfile.TemporaryDirectory(prefix="orphan-summary-") as directory:
        with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
            tar.extractall(directory, filter="data")
        return tree_count(Path(directory))


def summary(base: str, head: int, previous: int | None) -> str:
    lines = ["### Disconnected verified results (truth orphans)", "",
             "Root: STMT-CATHOLICISM-TRUE. Includes transcriptions; discovery, not certification.", "",
             "| Base revision | Base count | Head count | Delta (head − base) |",
             "| --- | ---: | ---: | ---: |"]
    if previous is None:
        lines += [f"| `{base}` | unavailable | {head} | unavailable |", "",
                  "Historical data unavailable: base revision could not be read or its frontier could not be computed. See step log. No zero baseline is assumed."]
    else:
        lines += [f"| `{base}` | {previous} | {head} | {head - previous:+d} |"]
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    head = tree_count(root)  # Head failures must fail CI, never become zero.
    try:
        previous = base_count(root, args.base)
    except (subprocess.CalledProcessError, OSError, ValueError, tarfile.TarError) as error:
        print(f"Orphan baseline unavailable: {error}", file=sys.stderr)
        if isinstance(error, subprocess.CalledProcessError):
            print(error.stderr, file=sys.stderr)
        previous = None
    print(summary(args.base, head, previous))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
