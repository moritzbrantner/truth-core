"""Guard the 2026-10-26 modal-ontology research intake against silent omissions.

This is an inventory integrity test, not a test of philosophical truth.
"""

import re
import unittest
from pathlib import Path


INVENTORY = Path(__file__).resolve().parents[1] / "docs" / "modal-ontology-120.md"
FIELDS = ("IMP", "MOD", "NEC", "EMP", "STA", "TIM", "CAU", "INF", "ACT", "EXP", "ONT", "EPI")
ENTRY = re.compile(r"^- \*\*([A-Z]{3})-([0-9]{2}) \(([FH])\)\*\* — (\S.+)$", re.MULTILINE)
SECTION = re.compile(r"^## ([A-Z]{3}) — ", re.MULTILINE)


class ModalOntologyInventoryTests(unittest.TestCase):
    def test_all_120_identifiers_are_present_exactly_once_and_in_order(self):
        content = INVENTORY.read_text(encoding="utf-8")
        matches = list(ENTRY.finditer(content))
        ids = [f"{match[1]}-{match[2]}" for match in matches]
        expected = [f"{field}-{index:02}" for field in FIELDS for index in range(1, 11)]
        self.assertEqual(ids, expected)
        self.assertEqual(len(ids), len(set(ids)))
        self.assertEqual(len(matches), 120)

    def test_all_twelve_topics_are_present(self):
        content = INVENTORY.read_text(encoding="utf-8")
        self.assertEqual(SECTION.findall(content), list(FIELDS))
        self.assertIn("Neither means proved", content)
        self.assertIn("not replacements for canonical `STMT-…` IDs", content)


if __name__ == "__main__":
    unittest.main()
