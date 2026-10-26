import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import docs_index as di  # noqa: E402


def entry(root: Path, relative: str, fields: dict[str, str], body: str) -> None:
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    front = "".join(f"{key}: {value}\n" for key, value in fields.items())
    path.write_text(f"---\n{front}---\n{body}\n")


class DocsIndexTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        entry(self.root, "docs/decisions/2026-10-24-01-b.md", {"date": "2026-10-24", "where": "#2"}, "Second\nline.")
        entry(self.root, "docs/decisions/2026-10-23-01-a.md", {"date": "2026-10-23", "where": "#1"}, "First.")
        (self.root / "docs/decisions/README.md").write_text("not an entry\n")
        entry(self.root, "docs/cands/x.md", {"group": "next"}, "Item **x**.\n\nMore about x.")
        entry(self.root, "docs/cands/y.md", {"group": "done"}, "Item y.")
        self.doc = self.root / "docs/case.md"
        self.doc.write_text(
            "# Case\n\nIntro.\n\n"
            '<!-- BEGIN GENERATED: docs/decisions table date=Date body=Principle "where=Where recorded" -->\n'
            "stale\n"
            "<!-- END GENERATED -->\n\n"
            "<!-- BEGIN GENERATED: docs/cands list filter:group=next -->\n"
            "<!-- END GENERATED -->\n\nOutro.\n"
        )

    def tearDown(self):
        self.tmp.cleanup()

    def test_render_table_and_list(self):
        self.assertIn(self.doc, di.stale(self.root))
        text = di.regenerate(self.root, self.doc)
        self.assertEqual(
            text,
            "# Case\n\nIntro.\n\n"
            '<!-- BEGIN GENERATED: docs/decisions table date=Date body=Principle "where=Where recorded" -->\n'
            "| Date | Principle | Where recorded |\n"
            "|---|---|---|\n"
            "| 2026-10-23 | First. | #1 |\n"
            "| 2026-10-24 | Second line. | #2 |\n"
            "<!-- END GENERATED -->\n\n"
            "<!-- BEGIN GENERATED: docs/cands list filter:group=next -->\n"
            "- Item **x**.\n"
            "\n"
            "  More about x.\n"
            "<!-- END GENERATED -->\n\nOutro.\n",
        )
        self.doc.write_text(text)
        self.assertEqual(di.stale(self.root), {})

    def test_missing_field_fails(self):
        entry(self.root, "docs/decisions/2026-10-25-01-c.md", {"date": "2026-10-25"}, "No where.")
        with self.assertRaises(di.DocsIndexError):
            di.regenerate(self.root, self.doc)

    def test_unclosed_section_fails(self):
        self.doc.write_text("<!-- BEGIN GENERATED: docs/cands list -->\n- x\n")
        with self.assertRaises(di.DocsIndexError):
            di.regenerate(self.root, self.doc)

    def test_table_without_body_column_needs_no_body(self):
        (self.root / "docs/rows").mkdir()
        (self.root / "docs/rows/a.md").write_text("---\npremise: P\nrival: R\n---\n")
        self.doc.write_text("<!-- BEGIN GENERATED: docs/rows table premise=Premise rival=Rival -->\n<!-- END GENERATED -->\n")
        self.assertIn("| P | R |", di.regenerate(self.root, self.doc))

    def test_list_entry_without_body_fails(self):
        (self.root / "docs/cands/z.md").write_text("---\ngroup: next\n---\n")
        with self.assertRaises(di.DocsIndexError):
            di.regenerate(self.root, self.doc)

    def test_pipe_in_cell_is_escaped(self):
        entry(self.root, "docs/decisions/2026-10-25-01-c.md", {"date": "2026-10-25", "where": "#3"}, "a | b")
        self.assertIn("| a \\| b |", di.regenerate(self.root, self.doc))

    def test_malformed_marker_fails(self):
        self.doc.write_text("<!--  BEGIN GENERATED: docs/cands list -->\n<!-- END GENERATED -->\n")
        with self.assertRaises(di.DocsIndexError):
            di.regenerate(self.root, self.doc)

    def test_repeated_key_fails(self):
        (self.root / "docs/cands/z.md").write_text("---\ngroup: a\ngroup: b\n---\nz\n")
        with self.assertRaises(di.DocsIndexError):
            di.regenerate(self.root, self.doc)

    def test_bad_entry_fails(self):
        (self.root / "docs/cands/z.md").write_text("no front matter\n")
        with self.assertRaises(di.DocsIndexError):
            di.regenerate(self.root, self.doc)


if __name__ == "__main__":
    unittest.main()
