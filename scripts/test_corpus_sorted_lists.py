#!/usr/bin/env python3
"""Tests for sorted order-free corpus lists. Run with:

    python3 -m unittest discover -s scripts -p 'test_*.py'
"""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))

import corpus  # noqa: E402


class SortedListsTest(unittest.TestCase):
    def test_sort_lists_sorts_and_keeps_format(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            sources = root / "corpus" / "sources"
            sources.mkdir(parents=True)
            pretty = sources / "pretty.json"
            pretty.write_text(json.dumps({"id": "S1", "edition_urns": ["b", "a"]}, indent=2) + "\n")
            oneline = sources / "oneline.json"
            oneline.write_text(json.dumps({"id": "S2", "edition_urns": ["d", "c"]}) + "\n")
            done = sources / "done.json"
            done.write_text('{"id": "S3", "edition_urns": ["a", "b"]}\n')
            with mock.patch.object(corpus, "ROOT", root), mock.patch.object(corpus, "CORPUS", root / "corpus"):
                self.assertEqual(
                    [(path.name, field) for path, field, _ in corpus.unsorted_lists()],
                    [("oneline.json", "edition_urns"), ("pretty.json", "edition_urns")],
                )
                with mock.patch("builtins.print"):
                    corpus.command_sort_lists(argparse.Namespace())
                self.assertEqual(corpus.unsorted_lists(), [])
            self.assertEqual(pretty.read_text(), json.dumps({"id": "S1", "edition_urns": ["a", "b"]}, indent=2) + "\n")
            self.assertEqual(oneline.read_text(), json.dumps({"id": "S2", "edition_urns": ["c", "d"]}) + "\n")


if __name__ == "__main__":
    unittest.main()
