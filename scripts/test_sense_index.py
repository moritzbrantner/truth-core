#!/usr/bin/env python3
"""Tests for sense-indexed terms (owner direction 2026-11-07)."""
from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))

import argument_batch  # noqa: E402
import corpus  # noqa: E402
import sense_index  # noqa: E402
import sense_labels  # noqa: E402

S1 = "11111111-1111-4111-8111-111111111111"
S2 = "22222222-2222-4222-9222-222222222222"
S3 = "33333333-3333-4333-a333-333333333333"
DISAMBIGUATION = {"id": "D", "term": "prior", "term_label": "PRIOR", "sense_definition_ids": ["DS", "DT", "DU"],
                  "senses": [{"id": S1, "label": "PRIOR_1", "definition_id": "DS"},
                             {"id": S2, "label": "PRIOR_2", "definition_id": "DT"},
                             {"id": S3, "label": "PRIOR_3", "definition_id": "DU"}]}


class TermLabelTest(unittest.TestCase):
    def test_normalize(self) -> None:
        self.assertEqual(sense_index.normalize_term("prior (simply, in time, or in substance)"), "PRIOR")
        self.assertEqual(sense_index.normalize_term("being (ens)"), "BEING")
        self.assertEqual(sense_index.normalize_term("in potency / mutable"), "IN_POTENCY_MUTABLE")

    def test_short_labels_are_unique_and_trimmed(self) -> None:
        labels = sense_index.short_term_labels([
            "reception of esse versus external cause of esse",
            "reception of esse versus external cause of motion",
            "cause", "cause",
        ])
        self.assertEqual(labels["cause"], "CAUSE")
        first = labels["reception of esse versus external cause of esse"]
        second = labels["reception of esse versus external cause of motion"]
        self.assertNotEqual(first, second)
        self.assertFalse(first.endswith("_OF"))

    def test_insert_fields_keeps_existing_text(self) -> None:
        text = '{\n  "id": "D",\n  "term": "\\u00e9"\n}\n'
        out = sense_index.insert_fields(text, {"term_label": "E"})
        self.assertTrue(out.startswith('{\n  "id": "D",\n  "term": "\\u00e9",\n  "term_label": "E"'))
        self.assertEqual(json.loads(out)["term_label"], "E")


class SenseRulesTest(unittest.TestCase):
    def test_bridged_needs_a_connected_component(self) -> None:
        bridge = {"term": "PRIOR", "from": S3, "to": S1, "statement_id": "STMT-B"}
        self.assertTrue(corpus.bridged("PRIOR", {S1, S3}, [bridge]))
        self.assertFalse(corpus.bridged("PRIOR", {S1, S2}, [bridge]))
        self.assertFalse(corpus.bridged("PRIOR", {S1, S3}, [{**bridge, "term": "CAUSE"}]))

    def test_uuid4(self) -> None:
        self.assertTrue(corpus.is_uuid4(S1))
        self.assertFalse(corpus.is_uuid4(S3.upper()))
        self.assertFalse(corpus.is_uuid4("11111111-1111-1111-8111-111111111111"))


class SenseLabelsTest(unittest.TestCase):
    def test_record_labels(self) -> None:
        statements = {"STMT-A": {"id": "STMT-A", "definition_ids": ["DS"]},
                      "STMT-B": {"id": "STMT-B", "definition_ids": ["DU"]}}
        by_definition = sense_labels.senses_by_definition([DISAMBIGUATION])
        argument = {"id": "ARG", "premise_statement_ids": ["STMT-B"], "conclusion_statement_id": "STMT-A"}
        self.assertEqual(sense_labels.record_sense_labels(statements["STMT-A"], statements, by_definition),
                         {"PRIOR": ["PRIOR_1"]})
        self.assertEqual(sense_labels.record_sense_labels(argument, statements, by_definition),
                         {"PRIOR": ["PRIOR_1", "PRIOR_3"]})
        result = {"id": "RES", "argument_id": "ARG"}
        self.assertEqual(sense_labels.record_sense_labels(result, statements, by_definition, {"ARG": argument}),
                         {"PRIOR": ["PRIOR_1", "PRIOR_3"]})
        self.assertEqual(sense_labels.format_sense_labels({"PRIOR": ["PRIOR_1"], "CAUSE": ["CAUSE_2"]}),
                         "PRIOR_1, CAUSE_2")


class SenseBindTest(unittest.TestCase):
    CONSTANTS = {"PRIOR": {S1: "N.PriorSimply", S2: "N.PriorInTime", S3: None}}
    STATEMENTS = {"STMT-BRIDGE": {"lean_declaration": "N.TimeIsSimple"}}

    def described(self, hypothesis_senses, result_senses, head="N.ActPrior"):
        return {"theorem": "N.t",
                "binders": [{"name": "h", "prop": True, "head": head, "senses": hypothesis_senses},
                            {"name": "x", "prop": False, "head": None}],
                "result": {"prop": True, "head": "N.Concl", "senses": result_senses}}

    def problems(self, described, argument=None):
        argument = argument or {"term_senses": {"PRIOR": S1}}
        return corpus.sense_bind_problems({"id": "R"}, argument, described, self.STATEMENTS, self.CONSTANTS)

    def test_declared_sense_only(self) -> None:
        self.assertEqual(self.problems(self.described(["N.PriorSimply"], [])), [])

    def test_other_sense_is_reported(self) -> None:
        kinds = [p["kind"] for p in self.problems(self.described(["N.PriorSimply"], ["N.PriorInTime"]))]
        self.assertEqual(kinds, ["other-sense-mentioned"])

    def test_declared_sense_must_occur(self) -> None:
        kinds = [p["kind"] for p in self.problems(self.described([], []))]
        self.assertEqual(kinds, ["declared-sense-not-mentioned"])

    def test_bridge_premise_is_exempt(self) -> None:
        argument = {"term_senses": {"PRIOR": S1},
                    "sense_bridges": [{"term": "PRIOR", "from": S2, "to": S1, "statement_id": "STMT-BRIDGE"}]}
        described = self.described(["N.PriorInTime", "N.PriorSimply"], [], head="N.TimeIsSimple")
        self.assertEqual(self.problems(described, argument), [])

    def test_sense_without_declaration_and_missing_description(self) -> None:
        kinds = [p["kind"] for p in self.problems(self.described([], []), {"term_senses": {"PRIOR": S3}})]
        self.assertEqual(kinds, ["sense-without-lean-declaration"])
        described = self.described([], [])
        del described["result"]["senses"]
        self.assertEqual([p["kind"] for p in self.problems(described)], ["sense-description-missing"])


class SenseBindRolesTest(SenseBindTest):
    def test_conclusion_bridge_exempts_the_result(self) -> None:
        argument = {"term_senses": {"PRIOR": S1}, "sense_bridges": [
            {"term": "PRIOR", "from": S1, "to": S2, "statement_id": "STMT-C", "role": "conclusion"}]}
        described = self.described(["N.PriorSimply"], ["N.PriorSimply", "N.PriorInTime"])
        self.assertEqual(self.problems(described, argument), [])

    def test_control_is_exempt(self) -> None:
        argument = {"term_senses": {"PRIOR": S1}, "sense_mixing_control": True}
        self.assertEqual(self.problems(self.described(["N.PriorInTime"], []), argument), [])

    def test_parameter_instantiated_with_another_predicate(self) -> None:
        # STMT-GOD links the PRIOR_1 sense, but its bound hypothesis instantiates
        # the declaration's predicate parameter with a nominal predicate.
        statements = {**self.STATEMENTS, "STMT-GOD": {"definition_ids": ["DS"]}}
        described = self.described([], ["N.PriorSimply"])
        binding = {"premises": [{"hypothesis": "h", "statement_id": "STMT-GOD"}], "conclusion": None}
        problems = corpus.sense_bind_problems({"id": "R"}, {"term_senses": {"PRIOR": S1}}, described, statements,
                                              self.CONSTANTS, {"DS": {S1}}, binding)
        self.assertEqual([p["kind"] for p in problems], ["statement-sense-not-instantiated"])
        described = self.described(["N.PriorSimply"], ["N.PriorSimply"])
        self.assertEqual(corpus.sense_bind_problems({"id": "R"}, {"term_senses": {"PRIOR": S1}}, described,
                                                    statements, self.CONSTANTS, {"DS": {S1}}, binding), [])


class EfficientRegressGodBindingTest(unittest.TestCase):
    def test_matching_head_cannot_hide_wrong_god_predicate(self):
        root = Path(__file__).resolve().parents[1]
        god = json.loads((root / "corpus/disambiguations/god.json").read_text())
        classical = next(s for s in god["senses"] if s["label"] == "GOD_4")
        constants = {"GOD": {s["id"]: s.get("lean_declaration") for s in god["senses"]}}
        statements = {s["id"]: s for _, s in corpus.load_dir("statements")}
        definition_senses = {s["definition_id"]: {s["id"]} for s in god["senses"]}
        paths = sorted((root / "corpus/arguments").glob(
            "CATHOLICISM-FROM-EFFICIENT-REGRESS-WITH-CLASSICAL-ATTRIBUTES*.json"))
        self.assertEqual(len(paths), 4)
        for path in paths:
            with self.subTest(argument=path.stem):
                argument = json.loads(path.read_text())
                self.assertEqual(argument["term_senses"]["GOD"], classical["id"])
                statement = next(statements[sid] for sid in argument["premise_statement_ids"]
                                 if statements[sid].get("legacy_id") == "STMT-GOD-NAMES-THE-FULLY-DESCRIBED-PRINCIPLE")
                # Same generic declaration head in both cases. A separate classical
                # hypothesis must not mask the wrong instantiation of hFull.
                described = {"binders": [
                    {"name": "hFull", "prop": True, "head": statement["lean_declaration"],
                     "senses": [classical["lean_declaration"]]},
                    {"name": "hOther", "prop": True, "senses": [classical["lean_declaration"]]}],
                    "result": {"senses": []}}
                binding = {"premises": [{"hypothesis": "hFull", "statement_id": statement["id"]}]}
                def problems():
                    return corpus.sense_bind_problems({}, argument, described, statements,
                                                      constants, definition_senses, binding)
                self.assertEqual(problems(), [])
                described["binders"][0]["senses"] = []
                self.assertEqual([p["kind"] for p in problems()], ["statement-sense-not-instantiated"])


class RatchetTest(unittest.TestCase):
    def test_identity_migration_is_not_an_added_exception(self):
        from corpus_ids import Aliases, legacy_uuid
        argument = legacy_uuid("argument", "A")
        aliases = Aliases([("argument", {"id": argument, "legacy_id": "A", "label": "A consequence"})])
        base = {"arguments": {"A": {"PRIOR": [S1]}}}
        migrated = {"arguments": {argument: {"PRIOR": [S1]}}}
        self.assertEqual(sense_index.allowlist_entries(base, aliases),
                         sense_index.allowlist_entries(migrated, aliases))
        grown = {"arguments": {argument: {"PRIOR": [S1, S2]}}}
        self.assertEqual(sense_index.allowlist_entries(grown, aliases)
                         - sense_index.allowlist_entries(base, aliases), {(argument, "PRIOR", S2)})

    def test_flat_entries(self) -> None:
        data = {"arguments": {"A": {"PRIOR": [S1, S2]}}, "senses_without_lean_declaration": [S3]}
        self.assertEqual(sense_index.allowlist_entries(data), {("A", "PRIOR", S1), ("A", "PRIOR", S2), (S3,)})
        grown = {"arguments": {"A": {"PRIOR": [S1, S2, S3]}}, "senses_without_lean_declaration": [S3]}
        self.assertEqual(sense_index.allowlist_entries(grown) - sense_index.allowlist_entries(data),
                         {("A", "PRIOR", S3)})


class ForEachSenseTest(unittest.TestCase):
    TABLE = {"PRIOR": {"PRIOR_1": S1, S1: S1, "PRIOR_3": S3, S3: S3}}

    def spec(self) -> dict:
        return {"argument": [{
            "label": "Act is prior", "rule": "r", "meaning": "m",
            "for_each_sense": {"term": "PRIOR", "senses": ["PRIOR_1", "PRIOR_3"]},
            "cases": {"PRIOR_1": {"theorem": "t1", "premises": ["STMT-P1"], "conclusion": "STMT-C1"},
                      "PRIOR_3": {"theorem": "t3", "premises": ["STMT-P3"], "conclusion": "STMT-C3"}},
        }]}

    def test_one_argument_per_sense_with_uuid_ids(self) -> None:
        with mock.patch.object(argument_batch, "sense_table", return_value=self.TABLE):
            cases = argument_batch.expand_sense_forks(self.spec(), {})
        self.assertEqual([case["term_senses"] for case in cases], [{"PRIOR": S1}, {"PRIOR": S3}])
        self.assertEqual([case["label"] for case in cases], ["Act is prior [PRIOR_1]", "Act is prior [PRIOR_3]"])
        self.assertTrue(all(corpus.is_uuid4(case["id"]) for case in cases))
        self.assertEqual([case["theorem"] for case in cases], ["t1", "t3"])

    def test_existing_ids_are_reused(self) -> None:
        existing = {"0d4b9c1e-0000-4000-8000-000000000000": (Path("x"), {
            "label": "Act is prior [PRIOR_3]", "term_senses": {"PRIOR": S3}, "inference_ids": ["INF-X"]})}
        with mock.patch.object(argument_batch, "sense_table", return_value=self.TABLE):
            cases = argument_batch.expand_sense_forks(self.spec(), existing)
        self.assertEqual(cases[1]["id"], "0d4b9c1e-0000-4000-8000-000000000000")
        self.assertEqual(cases[1]["inference_id"], "INF-X")

    def test_cases_must_match_senses(self) -> None:
        spec = self.spec()
        del spec["argument"][0]["cases"]["PRIOR_3"]
        with mock.patch.object(argument_batch, "sense_table", return_value=self.TABLE), \
                self.assertRaises(SystemExit):
            argument_batch.expand_sense_forks(spec, {})

    def test_plain_argument_senses_resolve_labels(self) -> None:
        spec = {"argument": [{"id": "A", "senses": {"PRIOR": "PRIOR_1"}}]}
        with mock.patch.object(argument_batch, "sense_table", return_value=self.TABLE):
            self.assertEqual(argument_batch.expand_sense_forks(spec, {})[0]["term_senses"], {"PRIOR": S1})
        with mock.patch.object(argument_batch, "sense_table", return_value=self.TABLE), \
                self.assertRaises(SystemExit):
            argument_batch.expand_sense_forks({"argument": [{"id": "A", "senses": {"PRIOR": "PRIOR_2"}}]}, {})


if __name__ == "__main__":
    unittest.main()
