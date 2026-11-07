#!/usr/bin/env python3
"""Tests for scripts/merge_queue.py."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import merge_queue  # noqa: E402


class GeneratedPathTest(unittest.TestCase):
    def test_only_aggregators_and_root_are_generated(self) -> None:
        self.assertTrue(merge_queue.is_generated("TruthCore/Imports/Results/Causality.lean"))
        self.assertTrue(merge_queue.is_generated("TruthCore.lean"))
        self.assertFalse(merge_queue.is_generated("TruthCore/Causality/Foo.lean"))
        self.assertFalse(merge_queue.is_generated("corpus/statements/foo.json"))
        self.assertFalse(merge_queue.is_generated("docs/catholic-case.md"))


if __name__ == "__main__":
    unittest.main()
