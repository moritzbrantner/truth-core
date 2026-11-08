"""Lean integration tests follow the workflow's selected verification scope."""
import unittest
from unittest.mock import patch

import lean_test_support as support


class LeanTestScopeTests(unittest.TestCase):
    def test_metadata_only_ci_skips_even_with_cached_modules(self):
        with patch.dict(support.os.environ, {"CI": "true", "TRUTH_CORE_LEAN_TESTS": "false"}), \
                patch.object(support, "missing_modules", return_value=[]):
            self.assertIn("metadata-only", support.build_skip_reason("Example"))

    def test_selected_ci_never_skips_missing_modules(self):
        with patch.dict(support.os.environ, {"CI": "true", "TRUTH_CORE_LEAN_TESTS": "true"}), \
                patch.object(support, "missing_modules", return_value=["Example"]):
            self.assertIsNone(support.build_skip_reason("Example"))

    def test_local_missing_modules_still_explain_how_to_build(self):
        with patch.dict(support.os.environ, {}, clear=True), \
                patch.object(support, "missing_modules", return_value=["Example"]):
            self.assertIn("lake build Example", support.build_skip_reason("Example"))
