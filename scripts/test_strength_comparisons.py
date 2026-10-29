"""Negative registrations and stale-evidence regressions for comparison presentation."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import strength_comparisons as strength


def fixture():
    statements = {sid: {"id": sid, "lean_declaration": "TruthCore.Test." + sid} for sid in ("S", "W", "D", "G", "R")}
    results = {role: {"id": role, "argument_id": role, "theorem": "Proof." + role} for role in strength.ROLES | {"separator"}}
    arguments = {role: {"id": role} for role in results}
    relation = {"id": "REL-TEST", "predicate": strength.PREDICATE,
                "subject_kind": "statement", "subject_id": "S", "object_kind": "statement", "object_id": "W",
                "delta_statement_id": "D", "background_statement_ids": [], "comparison_spec": "TruthCore.Test.spec",
                "evidence_result_ids": {role: role for role in strength.EXACT_DELTA_ROLES}, "note": "Explicit local interpretation."}
    data = {"statements": statements, "results": results, "arguments": arguments, "definitions": {}, "disambiguations": {}, "comparisons": [relation]}
    return relation, data


def binding(relation, data):
    fields = [("stronger", "subject_id"), ("weaker", "object_id"), ("delta", "delta_statement_id")]
    field_bindings = [{"role": role, "declaration": data["statements"][relation[field]]["lean_declaration"], "bound": True} for role, field in fields]
    field_bindings += [{"role": f"background.{i}", "declaration": data["statements"][sid]["lean_declaration"], "bound": True} for i, sid in enumerate(relation["background_statement_ids"])]
    output = {"id": relation["id"], "specification": relation["comparison_spec"], "bound": True,
              "field_bindings": field_bindings, "delta_degenerate": False,
              "certificates": [{"role": role, "theorem": data["results"][rid]["theorem"], "bound": True} for role, rid in relation["evidence_result_ids"].items()]}
    if relation.get("separator"):
        output["separator"] = {"setting": relation["separator"]["setting"], "theorem": data["results"][relation["separator"]["result_id"]]["theorem"], "bound": True}
    return output


class StrengthComparisonsTest(unittest.TestCase):
    def test_producer_reuses_canonical_executable_gate_contract(self):
        import corpus
        relation, data = fixture()
        relation["evidence_result_ids"] = {"implication": "implication"}
        data["relations"] = {relation["id"]: relation}
        result = data["results"]["implication"]
        result.update(challenge_module="TruthCore.Case.Challenge", solution_module="TruthCore.Case.Solution",
                      comparator_config="results/implication/comparator.json", status="solution-present")
        config = {"challenge_module": result["challenge_module"], "solution_module": result["solution_module"],
                  "theorem_names": [result["theorem"]], "permitted_axioms": [], "enable_nanoda": True}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("Challenge", "Solution"):
                path = root / f"TruthCore/Case/{name}.lean"
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("-- fixture")
            path = root / result["comparator_config"]
            path.parent.mkdir(parents=True)
            loader = lambda kind: [(root / f"corpus/{kind}/{key}.json", value) for key, value in data[kind].items()]
            with patch.object(corpus, "ROOT", root):
                path.write_text(json.dumps(config))
                strength.context(root, loader)
                for changed, error in (({"theorem_names": []}, "theorem is not listed"), ({"enable_nanoda": False}, "NanoDa must be enabled")):
                    path.write_text(json.dumps({**config, **changed}))
                    with self.subTest(changed=changed), self.assertRaisesRegex(corpus.CorpusError, error):
                        strength.context(root, loader)
                path.write_text(json.dumps(config))
                result["comparator_config"] = "results/different/comparator.json"
                with self.assertRaisesRegex(corpus.CorpusError, "Comparator path must match"):
                    strength.context(root, loader)

    def test_registration_cannot_assert_strictness_or_status(self):
        relation, data = fixture()
        for field, value in (("strictly_stronger", True), ("status", "proved"), ("minimal", True), ("verified", True)):
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "not registration authority"):
                strength.validate_registration({**relation, field: value}, data["statements"], data["results"], data["arguments"])

    def test_unknown_background_or_evidence_rejected(self):
        relation, data = fixture()
        for changed in ({"background_statement_ids": ["missing"]}, {"evidence_result_ids": {"implication": "missing"}}):
            with self.assertRaises(ValueError):
                strength.validate_registration({**relation, **changed}, data["statements"], data["results"], data["arguments"])

    def test_sufficient_only_condition_is_not_exact_content(self):
        relation, data = fixture()
        relation["evidence_result_ids"] = {"reconstruction": "reconstruction", "implication": "implication"}
        report = strength.projection(relation, data, binding(relation, data), verified=True)
        self.assertEqual(report["comparison_status"], "proved implication")
        self.assertEqual(report["delta_status"], "sufficient only; exactness unresolved")
        self.assertIn("delta_forward", report["remaining_obligations"])
        self.assertEqual(report["converse_status"], "unresolved")

    def test_all_three_directions_and_iff_needed_for_exact_label(self):
        relation, data = fixture()
        full = strength.projection(relation, data, binding(relation, data), verified=True)
        self.assertEqual(full["delta_status"], "exact additional requirement proved")
        for missing in strength.EXACT_DELTA_ROLES:
            partial = copy.deepcopy(relation)
            del partial["evidence_result_ids"][missing]
            report = strength.projection(partial, data, binding(partial, data), verified=True)
            self.assertNotEqual(report["delta_status"], "exact additional requirement proved")

    def test_strictness_needs_separating_setting_same_background_binding(self):
        relation, data = fixture()
        no_separator = strength.projection(relation, data, binding(relation, data), verified=True)
        self.assertEqual(no_separator["comparison_status"], "proved implication")
        relation["separator"] = {"setting": "TruthCore.Test.setting", "result_id": "separator"}
        bound = binding(relation, data)
        strength.validate_binding(relation, data, bound)
        strict = strength.projection(relation, data, bound, verified=True)
        self.assertEqual(strict["comparison_status"], "strict strengthening")
        bound["separator"]["setting"] = "TruthCore.OtherBackground.setting"
        with self.assertRaisesRegex(ValueError, "same-background"):
            strength.validate_binding(relation, data, bound)

    def test_mismatched_role_arguments_background_or_identity_rejected(self):
        relation, data = fixture()
        relation["background_statement_ids"] = ["G"]
        for mutation in ("background", "theorem", "role", "bound"):
            with self.subTest(mutation=mutation):
                actual = binding(relation, data)
                if mutation == "background":
                    actual["field_bindings"][-1]["declaration"] = "TruthCore.Other.G"
                elif mutation == "theorem":
                    actual["certificates"][0]["theorem"] = "Proof.OtherArguments"
                elif mutation == "role":
                    actual["certificates"] = actual["certificates"][:-1]
                else:
                    actual["certificates"][0]["bound"] = False
                with self.assertRaises(ValueError):
                    strength.validate_binding(relation, data, actual)

    def test_degenerate_delta_not_explanatory_discovery(self):
        relation, data = fixture()
        actual = binding(relation, data)
        actual["delta_degenerate"] = True
        with self.assertRaisesRegex(ValueError, "not an explanatory"):
            strength.projection(relation, data, actual, verified=True)

    def test_registered_only_never_infers_proofs_from_result_presence(self):
        relation, data = fixture()
        report = strength.projection(relation, data)
        self.assertFalse(report["verified"])
        self.assertEqual(report["comparison_status"], "unresolved")
        self.assertEqual(report["delta_status"], "unresolved")

    def test_multiple_named_deltas_do_not_claim_uniqueness(self):
        relation, data = fixture()
        another = {**relation, "id": "REL-OTHER-DELTA", "delta_statement_id": "R"}
        strength.validate_registration(another, data["statements"], data["results"], data["arguments"])
        self.assertNotEqual(strength.projection(relation, data)["delta_statement_id"], strength.projection(another, data)["delta_statement_id"])

    def test_definition_change_invalidates_old_evidence_despite_same_ids(self):
        relation, data = fixture()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Definitions.lean"
            source.write_text("def relation (x y : Nat) := x < y")
            def manifest(_):
                return {"Definitions.lean": hashlib.sha256(source.read_bytes()).hexdigest()}
            with patch.object(strength, "input_manifest", manifest):
                current = manifest(root)
                report = strength.projection(relation, data, binding(relation, data), verified=True)
                artifact = {"schema_version": 1, "producer": {"mode": "live-verified", "trust": strength.TRUST,
                            "source_head": "informational", "inputs": current, "input_digest": strength.input_digest(current)}, "comparisons": [report]}
                path = root / "artifact.json"
                path.write_text(json.dumps(artifact))
                strength.read_bundle(root, path, data)
                source.write_text("def relation (x y : Nat) := x ≤ y")
                self.assertEqual(relation["subject_id"], "S")
                self.assertEqual(data["statements"]["S"]["lean_declaration"], "TruthCore.Test.S")
                with self.assertRaisesRegex(ValueError, "stale strength report"):
                    strength.read_bundle(root, path, data)


if __name__ == "__main__":
    unittest.main()
