#!/usr/bin/env python3
"""Resolve result handles through corpus records, preserving migrated config paths."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from corpus_ids import Aliases

ROOT = Path(__file__).resolve().parents[1]


def resolve_configs(root: Path, identifiers: list[str]) -> list[Path]:
    records = [json.loads(path.read_text(encoding="utf-8"))
               for path in sorted((root / "corpus/results").glob("*.json"))]
    aliases = Aliases(("result", record) for record in records)
    indexed = {record["id"]: record for record in records}
    configs = []
    for token in identifiers:
        result_id = aliases.resolve(token, ("result",))
        config = root / indexed[result_id]["comparator_config"] if result_id else None
        if config is None or not config.is_file():
            raise ValueError(f"unknown result or missing Comparator config: {token}")
        configs.append(config)
    return configs


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--modules", action="store_true")
    parser.add_argument("results", nargs="+")
    args = parser.parse_args()
    try:
        configs = resolve_configs(ROOT, args.results)
        if args.modules:
            modules = set()
            for path in configs:
                config = json.loads(path.read_text(encoding="utf-8"))
                modules.update((config["challenge_module"], config["solution_module"]))
            print("\n".join(sorted(modules)))
        else:
            print("\n".join(str(path) for path in configs))
        return 0
    except (ValueError, KeyError, OSError) as exc:
        print(exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
