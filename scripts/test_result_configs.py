"""Verifier config lookup follows record identity rather than record filenames."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from corpus_ids import legacy_uuid
import result_configs


class ResultConfigTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.result_id = legacy_uuid("result", "OLD-RESULT")
        self.config = self.root / "results/OLD-RESULT/comparator.json"
        self.config.parent.mkdir(parents=True)
        self.config.write_text(json.dumps({"challenge_module": "TruthCore.Test.Challenge",
                                           "solution_module": "TruthCore.Test.Solution"}))
        records = self.root / "corpus/results"
        records.mkdir(parents=True)
        (records / "unrelated-filename.json").write_text(json.dumps({
            "id": self.result_id, "legacy_id": "OLD-RESULT", "label": "An existing consequence",
            "comparator_config": "results/OLD-RESULT/comparator.json"}))

    def test_uuid_legacy_alias_and_label_use_recorded_path(self):
        for token in (self.result_id, "OLD-RESULT", "An existing consequence"):
            with self.subTest(token=token):
                self.assertEqual(result_configs.resolve_configs(self.root, [token]), [self.config])

    def test_modules_are_selected_from_resolved_configs(self):
        output = io.StringIO()
        with patch.object(result_configs, "ROOT", self.root), \
                patch("sys.argv", ["result_configs.py", "--modules", self.result_id, "OLD-RESULT"]), \
                contextlib.redirect_stdout(output):
            self.assertEqual(result_configs.main(), 0)
        self.assertEqual(output.getvalue().splitlines(),
                         ["TruthCore.Test.Challenge", "TruthCore.Test.Solution"])

    def test_unknown_result_or_missing_config_fails(self):
        with self.assertRaisesRegex(ValueError, "unknown result or missing"):
            result_configs.resolve_configs(self.root, ["missing"])
        self.config.unlink()
        with self.assertRaisesRegex(ValueError, "unknown result or missing"):
            result_configs.resolve_configs(self.root, [self.result_id])
