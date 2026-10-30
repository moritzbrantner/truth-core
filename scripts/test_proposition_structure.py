"""Pipeline regressions; elaborated expression semantics tested by the Lean fixture."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from proposition_structure import check_artifact, module_for, nodes, semantic_links


class PropositionStructureTests(unittest.TestCase):
    def test_longest_module_prefix_supports_structure_fields(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'TruthCore/Case').mkdir(parents=True)
            (root / 'TruthCore/Case/Root.lean').write_text('namespace TruthCore.Case.Root\nstructure S where\n  p : Prop\nend TruthCore.Case.Root')
            self.assertEqual(module_for(root, 'TruthCore.Case.Root.S.p'), 'TruthCore.Case.Root')

    def test_namespace_does_not_need_to_match_module(self):
        root = Path(__file__).resolve().parents[1]
        self.assertEqual(module_for(root, 'TruthCore.Case.Catholicism.GodHasClassicalAttributes'), 'TruthCore.Case.Catholicism.Root')
        self.assertEqual(module_for(root, 'TruthCore.Case.Catholicism.ClassicalAttributesSuffice'), 'TruthCore.Case.Catholicism.StageTwo')

    def test_semantic_links_are_not_formula_replacements(self):
        expression = [{"type": {"id": "root", "kind": "application", "declaration": "TruthCore.P", "children": [
            {"role": "argument.0", "node": {"id": "arg", "kind": "variable", "text": "x", "binding": "binder"}}]}}]
        definitions = [{"id": "DEF-P", "lean_declaration": "TruthCore.P", "definition": "P interpretation"},
                       {"id": "DEF-Q", "lean_declaration": "TruthCore.Q"}, {"id": "DEF-NO-LEAN"}]
        links = semantic_links({}, expression, definitions, [{"id": "DISAMB-P", "sense_definition_ids": ["DEF-P", "DEF-Q"]}])
        self.assertEqual(links['definitions'][0]['expression_ids'], ['root'])
        self.assertEqual(len(links['definitions']), 1)
        self.assertEqual(len(links['disambiguations']), 1)
        self.assertEqual(expression[0]['type']['kind'], 'application')
        contextual = semantic_links({'definition_ids': ['DEF-NO-LEAN']}, expression, [{'id': 'DEF-NO-LEAN'}], [])
        self.assertEqual(contextual['definitions'][0]['expression_ids'], [])
        self.assertEqual([n['id'] for n in nodes(expression)], ['root', 'arg'])

    def test_input_digest_head_is_informational_but_sources_bind(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'source.lean').write_text('P a b')
            inputs = [{"path": "source.lean", "sha256": hashlib.sha256(b'P a b').hexdigest()}]
            request = {"declarations": ["TruthCore.P"]}
            revision = {"head": "different merge SHA accepted", "inputs": inputs, "request": request,
                        "input_digest": hashlib.sha256(json.dumps({"request": request, "inputs": inputs}, sort_keys=True).encode()).hexdigest()}
            artifact = {"schema_version": 1, "reports": [{"revision": revision}]}
            check_artifact(root, artifact)
            (root / 'source.lean').write_text('P b a')
            with self.assertRaisesRegex(ValueError, 'stale structure artifact'):
                check_artifact(root, artifact)

    def test_missing_or_forged_artifact_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for artifact in [{}, {"schema_version": 1, "reports": []}]:
                with self.assertRaises(ValueError):
                    check_artifact(root, artifact)
            with self.assertRaisesRegex(ValueError, 'digest'):
                check_artifact(root, {"schema_version": 1, "reports": [{"revision": {"inputs": [], "request": {}, "input_digest": "forged"}}]})


if __name__ == '__main__':
    unittest.main()
