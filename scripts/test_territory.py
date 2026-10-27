"""Emergent positions and the territory matrix (#512)."""
from contextlib import redirect_stdout
import io
import json
import unittest

import corpus
from territory import FALSE_DECLARATION, position_id, territory_report


def argument(aid, premises, conclusion, **extra):
    return {"id": aid, "premise_statement_ids": premises, "conclusion_statement_id": conclusion, **extra}


class TerritoryFixtureTests(unittest.TestCase):
    def setUp(self):
        ids = ["P", "Q", "R", "S", "T", "U", "V", "W", "Y", "X", "THEORY", "FALSE"]
        self.statements = {sid: {"id": sid, "lean_declaration": "Fixture." + sid} for sid in ids}
        self.statements["FALSE"]["lean_declaration"] = FALSE_DECLARATION
        self.arguments = {a["id"]: a for a in [
            argument("CORE", ["P", "R"], "FALSE"),
            argument("QR", ["Q"], "R"),
            argument("QX", ["Q"], "X"),
            argument("YW", ["Y"], "S"),
            argument("TRANSCRIBED-CORE", ["S", "T"], "FALSE"),
            argument("CONSISTENT", [], "THEORY", commitment_statement_ids=["Q", "R"]),
        ]}
        self.results = {aid: {"id": aid, "argument_id": aid, "theorem": "Fixture." + aid} for aid in self.arguments}
        self.relations = [
            {"id": "REL-V-ALT-U", "predicate": "alternative_to", "subject_id": "V", "object_id": "U"},
            {"id": "REL-YW-REFUTES-W", "predicate": "refutes", "subject_id": "YW", "object_id": "W"},
            {"id": "REL-W-ALT-S", "predicate": "alternative_to", "subject_id": "W", "object_id": "S"},
        ]
        self.sources = {"SRC-A": {"id": "SRC-A", "author": "Aquinas"}, "SRC-H": {"id": "SRC-H", "author": "Hume"}}
        self.claims = [
            {"id": "C-P", "statement_id": "P", "source_id": "SRC-A"},
            {"id": "C-Q", "statement_id": "Q", "source_id": "SRC-H"},
            {"id": "C-R", "statement_id": "R", "source_id": "SRC-H"},
            {"id": "C-R2", "statement_id": "R", "source_id": "SRC-A"},
        ]
        self.models = [{"id": "MODEL-PT", "evaluations": [
            {"statement_id": "P", "value": "satisfies"}, {"statement_id": "T", "value": "satisfies"},
            {"statement_id": "Q", "value": "violates"}]}]
        self.seeds = [{"statement_id": sid, "transitive_dependent_arguments": ["A"] * n}
                      for sid, n in [("P", 1), ("Q", 3), ("S", 2), ("T", 1), ("U", 1)]]
        self.routes = [{"argument_id": "ROUTE", "verified": True, "cost": 2, "open_premise_statement_ids": ["P", "Q"]},
                       {"argument_id": "ROUTE-2", "verified": True, "cost": 3, "open_premise_statement_ids": ["Q", "S", "T"]}]

    def report(self, **bounds):
        return territory_report(statements=self.statements, arguments=self.arguments, results=self.results,
                                relations=self.relations, claims=self.claims, sources=self.sources, models=self.models,
                                transcription_results={"TRANSCRIBED-CORE"}, seeds=self.seeds, routes=self.routes, **bounds)

    def test_core_pruning_through_entailment(self):
        report = self.report()
        conflicts = sorted(conflict["statement_ids"] for conflict in report["conflicts"])
        # Q entails R, so Q with P also meets the certified core; the transcription is no core.
        self.assertEqual(conflicts, [["P", "Q"], ["P", "R"], ["W", "Y"]])
        component = next(c for c in report["components"] if "P" in c["atom_ids"])
        positions = sorted(next(p for p in report["positions"] if p["id"] == pid)["atom_ids"] for pid in component["position_ids"])
        self.assertEqual(positions, [["P"], ["Q", "R"]])

    def test_entailment_closure_and_stable_ids(self):
        positions = {tuple(p["atom_ids"]): p for p in self.report()["positions"]}
        qr = positions[("Q", "R")]
        self.assertEqual(qr["id"], position_id(["R", "Q"]))
        self.assertIn("X", qr["entailed_statement_ids"])
        self.assertNotIn(("Q",), positions)  # Q without R would not be closed
        self.assertEqual(self.report(), self.report())

    def test_witnessed_versus_not_known_inconsistent(self):
        positions = {tuple(p["atom_ids"]): p for p in self.report()["positions"]}
        self.assertEqual(positions[("P",)]["status"], "witnessed")
        self.assertEqual(positions[("P",)]["witnesses"], [{"kind": "model", "id": "MODEL-PT"}])
        # A consistency result witnesses its commitment set.
        self.assertEqual(positions[("Q", "R")]["witnesses"], [{"kind": "consistency_result", "id": "CONSISTENT"}])
        self.models = []
        del self.arguments["CONSISTENT"], self.results["CONSISTENT"]
        positions = {tuple(p["atom_ids"]): p for p in self.report()["positions"]}
        self.assertEqual(positions[("Q", "R")]["status"], "not_known_inconsistent")

    def test_attestation_is_computed_from_claims(self):
        positions = {tuple(p["atom_ids"]): p for p in self.report()["positions"]}
        self.assertEqual(positions[("Q", "R")]["attested_by"], ["Hume"])
        partial = {row["author"]: row for row in positions[("Q", "R")]["stating_authors"]}
        self.assertFalse(partial["Aquinas"]["covers_all"])
        self.assertEqual(partial["Aquinas"]["claim_ids"], ["C-R2"])
        self.assertEqual(positions[("P",)]["attested_by"], ["Aquinas"])

    def test_agreement_split_and_contested_rows(self):
        report = self.report()
        rows = {row["statement_id"]: row for row in report["matrix"]}
        self.assertEqual(rows["P"]["classification"], "split")
        self.assertEqual(rows["Q"]["classification"], "split")
        self.assertEqual(rows["T"]["classification"], "common_ground_candidate")
        self.assertEqual(rows["U"]["classification"], "contested_uncertified")
        self.assertEqual(rows["U"]["rivals"], [{"statement_id": "V", "class": "uncertified"}])
        self.assertEqual(rows["S"]["rivals"], [{"statement_id": "W", "class": "uncertified"}])
        self.assertEqual(report["common_ground_candidates"], ["T"])
        # Territories ranked by root routes, then dependents.
        self.assertEqual([row["statement_id"] for row in report["territories"]][:2], ["Q", "P"])
        p_positions = {p["id"]: p for p in report["positions"]}
        for pid, value in rows["P"]["values"].items():
            if "P" in p_positions[pid]["atom_ids"]:
                self.assertEqual(value, "in")
            elif value == "out":
                self.assertTrue(set(p_positions[pid]["atom_ids"]) & {"Q", "R"})
        self.assertIn("undetermined", rows["P"]["values"].values())

    def test_certified_incompatible_rival_and_global_product(self):
        self.relations.append({"id": "REL-R-ALT-P", "predicate": "alternative_to", "subject_id": "R", "object_id": "P"})
        report = self.report()
        rows = {row["statement_id"]: row for row in report["matrix"]}
        self.assertEqual(rows["P"]["rivals"], [{"statement_id": "R", "class": "certified_incompatible"}])
        counts = [len(c["position_ids"]) for c in report["components"]]
        expected = 1
        for count in counts:
            expected *= count
        self.assertEqual(report["global_positions"]["count"], expected)
        self.assertEqual(len(self.report(global_position_limit=1)["global_positions"]["positions"]), 1)

    def test_truncated_enumeration_withholds_positions(self):
        report = self.report(hitting_set_limit=1)
        positions = [set(p["atom_ids"]) for p in report["positions"]]
        conflicts = [set(c["statement_ids"]) for c in report["conflicts"]]
        self.assertFalse(any(c <= p for c in conflicts for p in positions))
        rows = {row["statement_id"]: row for row in report["matrix"]}
        self.assertEqual(rows["P"]["classification"], "enumeration_truncated")
        self.assertIsNone(report["global_positions"]["count"])
        self.assertTrue(report["global_positions"]["truncated"])

    def test_rival_eliminated_in_another_component(self):
        self.arguments["R-ONLY"] = argument("R-ONLY", ["V"], "FALSE")
        self.results["R-ONLY"] = {"id": "R-ONLY", "argument_id": "R-ONLY", "theorem": "Fixture.R-ONLY"}
        rows = {row["statement_id"]: row for row in self.report()["matrix"]}
        self.assertEqual(rows["U"]["classification"], "rivals_eliminated")

    def test_witness_of_a_conflict_is_a_defect(self):
        self.models[0]["evaluations"].append({"statement_id": "R", "value": "satisfies"})
        self.assertEqual([d["kind"] for d in self.report()["defects"]], ["witness_satisfies_conflict"])


class TerritoryRealCorpusTests(unittest.TestCase):
    def test_structural_invariants(self):
        output = io.StringIO()
        with redirect_stdout(output):
            self.assertEqual(corpus.main_with(["territory", "--json"]), 0)
        report = json.loads(output.getvalue())
        conflicts = [set(c["statement_ids"]) for c in report["conflicts"]]
        positions = {p["id"]: p for p in report["positions"]}
        universe = set(report["universe"])
        self.assertEqual(report["defects"], [])
        if not report["bounds"]["universe_truncated"]:
            self.assertTrue(set(report["inputs"]["seed_statement_ids"]) <= universe)
        for pid, position in positions.items():
            atoms = set(position["atom_ids"])
            self.assertEqual(pid, position_id(atoms))
            self.assertFalse(any(conflict <= atoms for conflict in conflicts))
            self.assertEqual(position["status"] == "witnessed", bool(position["witnesses"]))
            for author in position["attested_by"]:
                row = next(r for r in position["stating_authors"] if r["author"] == author)
                self.assertEqual(set(row["statement_ids"]), atoms)
        for component in report["components"]:
            members = set(component["atom_ids"])
            for pid in component["position_ids"]:
                atoms = set(positions[pid]["atom_ids"])
                # Maximal: every excluded member conflicts with the position.
                for atom in members - atoms:
                    self.assertTrue(any(atom in c and c <= atoms | {atom} for c in conflicts))
        for row in report["matrix"]:
            self.assertTrue(set(row["values"].values()) <= {"in", "out", "undetermined"})
            if row["classification"] == "common_ground_candidate":
                self.assertFalse(row["rivals"])
                self.assertTrue(row["witnessed_in_position_ids"])
                self.assertFalse(row["out_position_ids"])
        self.assertEqual(report["common_ground_candidates"],
                         [r["statement_id"] for r in report["matrix"] if r["classification"] == "common_ground_candidate"])


if __name__ == "__main__":
    unittest.main()
