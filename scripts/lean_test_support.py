"""Skip Lean integration tests cleanly when their build output is missing (#990).

Some unit tests elaborate fixtures that import compiled `TruthCore` modules. In a
fresh clone without `.lake/build` they used to fail with a long Lean error. They
now skip with the exact module and command to build it. On CI (`CI` set) they
never skip: a missing build there is a real failure.
"""

from __future__ import annotations

import os
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BUILD_LIB = ROOT / ".lake" / "build" / "lib" / "lean"


def missing_modules(*modules: str) -> list[str]:
    """The `TruthCore` modules among `modules` whose `.olean` is not built."""
    return [
        module
        for module in modules
        if not (BUILD_LIB / Path(*module.split("."))).with_suffix(".olean").is_file()
    ]


def build_skip_reason(*modules: str) -> str | None:
    """Why a test needing `modules` must skip here, or None when it can run."""
    missing = missing_modules(*modules)
    if not missing or os.environ.get("CI"):
        return None
    return (
        f"needs built Lean modules ({', '.join(missing)} not in .lake/build); "
        f"run `lake build {' '.join(missing)}` or seed this clone (docs/worker-startup.md)"
    )


def requires_built(*modules: str):
    """Decorator: skip a test or test class until `modules` are built (never on CI)."""
    reason = build_skip_reason(*modules)
    return unittest.skipIf(reason is not None, reason or "")
