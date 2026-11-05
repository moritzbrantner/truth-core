#!/usr/bin/env python3
import contextlib
import copy
import io
import json
import shutil
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import corpus
from argument_context import context_pack, format_context, import_closure, lean_reuse_review, resolve_target, theorem_blocks

CHALLENGE = """import Demo.Vocabulary
namespace Demo.Up

/-- Advertised. -/
theorem main {B : Type} (P Q : B → Prop)
    (hP : PremiseP P) (hQ : PremiseQ Q) :
    Conclusion P Q := by
  sorry

theorem withoutP : FailsWithoutP := by
  sorry
end Demo.Up
"""


def write(root: Path, module: str, text: str) -> None:
    path = root / (module.replace(".", "/") + ".lean")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


class ArgumentContextTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        write(self.root, "TruthCore.Up.Challenge", CHALLENGE)
        write(self.root, "TruthCore.Up.Solution", "import TruthCore.Base.Solution\n")
        write(self.root, "TruthCore.Base.Solution", "import TruthCore.Deep.Solution\nimport Mathlib.Order.Basic\n")
        write(self.root, "TruthCore.Deep.Solution", "")
        write(self.root, "TruthCore.Down.Solution", "import TruthCore.Up.Solution\n")
        write(self.root, "TruthCore.Up.Solution", "import TruthCore.Base.Solution\nimport TruthCore.Vocab\n")
        write(self.root, "TruthCore.Peer.Solution", "import TruthCore.Vocab\n")
        write(self.root, "TruthCore.Far.Solution", "import TruthCore.Down.Solution\n")
        (self.root / "results/UP").mkdir(parents=True)
        (self.root / "results/UP/comparator.json").write_text(json.dumps(
            {"theorem_names": ["Demo.Up.main"], "permitted_axioms": []}), encoding="utf-8")
        result = lambda rid, arg, module, **extra: {"id": rid, "argument_id": arg, "theorem": f"Demo.{module}.main",
                                                    "solution_module": f"TruthCore.{module}.Solution", "status": "solution-present", **extra}
        self.data = {
            "statements": [{"id": sid, "paraphrase": f"{sid} paraphrase", "lean_declaration": f"Demo.{sid}"}
                           for sid in ["P", "Q", "C", "D", "X"]],
            "claims": [{"id": "CLAIM-Q", "statement_id": "Q"}],
            "definitions": [{"id": "DEF-C", "definition": "C means C."}],
            "disambiguations": [],
            "inferences": [{"id": "INF-UP", "input_statement_ids": ["P", "Q"], "output_statement_id": "C", "rule": "verified-result"}],
            "arguments": [
                {"id": "UP", "premise_statement_ids": ["P", "Q"], "conclusion_statement_id": "C", "inference_ids": ["INF-UP"],
                 "meaning": "P and Q jointly give C.", "definition_ids": ["DEF-C"]},
                {"id": "BASE", "premise_statement_ids": ["X"], "conclusion_statement_id": "P", "inference_ids": []},
                {"id": "DEEP", "premise_statement_ids": [], "conclusion_statement_id": "X", "inference_ids": []},
                {"id": "DOWN", "premise_statement_ids": ["C"], "conclusion_statement_id": "D", "inference_ids": []},
                {"id": "TWIN", "premise_statement_ids": ["Q", "P"], "conclusion_statement_id": "C", "inference_ids": []},
                {"id": "PEER", "premise_statement_ids": ["Q"], "conclusion_statement_id": "X", "inference_ids": []},
                {"id": "FAR", "premise_statement_ids": ["D"], "conclusion_statement_id": "X", "inference_ids": []},
            ],
            "results": [
                result("UP", "UP", "Up", challenge_module="TruthCore.Up.Challenge", comparator_config="results/UP/comparator.json"),
                result("BASE", "BASE", "Base"), result("DEEP", "DEEP", "Deep"), result("DOWN", "DOWN", "Down"), result("PEER", "PEER", "Peer"), result("FAR", "FAR", "Far"),
            ],
            "relations": [{"id": "REL-ALT", "subject_id": "Q", "predicate": "alternative_to", "object_id": "D"},
                          {"id": "REL-SUP", "subject_id": "CLAIM-Q", "predicate": "supports", "object_id": "Q"}],
            "attempts": [
                {"id": "ATTEMPT-OLD", "statement_ids": ["Q"], "date": "2026-10-01", "kind": "derivation", "outcome": "blocked",
                 "summary": "Tried to derive Q.", "evidence": [], "blocker": "Q needs a bridge."},
                {"id": "ATTEMPT-NEW", "statement_ids": ["X"], "date": "2026-10-02", "kind": "reading", "outcome": "succeeded",
                 "summary": "Cites the result.", "evidence": ["UP"]},
                {"id": "ATTEMPT-ELSEWHERE", "statement_ids": ["X"], "date": "2026-10-03", "kind": "reading", "outcome": "failed",
                 "summary": "Unrelated.", "evidence": []},
            ],
            "models": [{"id": "MODEL-M", "evaluations": [
                {"statement_id": "P", "value": "satisfies", "theorem": "Demo.m.p", "arguments": []},
                {"statement_id": "Q", "value": "violates", "theorem": "Demo.m.q", "arguments": []},
                {"statement_id": "X", "value": "violates", "theorem": "Demo.m.x", "arguments": []}]}],
            "configurations": [{"id": "CONFIG-C", "seed_statement_id": "C", "semantics": {"id": "sem", "applications": {"Q": {}}}}],
            "candidates": [{"id": "CAND-Q", "status": "candidate", "priority": 3, "goal": "Defend Q for UP.", "reason": ""},
                           {"id": "CAND-QX", "status": "candidate", "priority": 4, "goal": "Mentions QX and STMT-Q only.", "reason": ""}],
        }
        self.report = corpus.frontier_report(self.data["statements"], self.data["arguments"], self.data["results"],
                                             self.data["relations"], root="D", claims=self.data["claims"])

    def tearDown(self):
        self.tmp.cleanup()

    def pack(self):
        return context_pack(self.root, self.data, self.report, "UP")

    def test_frozen_theorem_text_and_companions_come_from_lean_source(self):
        blocks = theorem_blocks(self.root, "TruthCore.Up.Challenge")
        self.assertEqual([b["name"] for b in blocks], ["main", "withoutP"])
        self.assertTrue(blocks[0]["statement"].startswith("theorem main {B : Type}"))
        self.assertTrue(blocks[0]["statement"].endswith("Conclusion P Q"))
        self.assertEqual(blocks[0]["line"], 5)
        lean = self.pack()["lean"][0]
        self.assertEqual(lean["advertised_statement"]["name"], "main")
        self.assertEqual([(b["name"], b["comparator_checked"]) for b in lean["companion_theorems"]], [("withoutP", False)])
        self.assertEqual(self.pack()["unresolved"]["unchecked_companion_theorems"], ["UP:withoutP"])

    def test_lean_reuse_is_the_transitive_import_closure_mapped_to_results(self):
        self.assertEqual(import_closure(self.root, "TruthCore.Up.Solution"),
                         {"TruthCore.Base.Solution": 1, "TruthCore.Vocab": 1, "TruthCore.Deep.Solution": 2})
        lean = self.pack()["lean"][0]
        reused = {(r["result_id"], r["depth"], r["graph_linked"]) for r in lean["reused_results"]}
        # BASE concludes premise P, so the graph records it; DEEP is reached only through imports.
        self.assertEqual(reused, {("BASE", 1, True), ("DEEP", 2, False)})
        self.assertEqual(lean["lean_consumers"], ["DOWN"])
        self.assertEqual(lean["lean_consumers_depth2"], ["FAR"])

    def test_module_system_headers_keep_imports_and_theorems_visible(self):
        write(self.root, "TruthCore.Base.Solution",
              "module\n\npublic import TruthCore.Deep.Solution\npublic import Mathlib.Order.Basic\n\n"
              "@[expose] public section\n\npublic theorem exported : True := trivial\n")
        self.assertEqual(import_closure(self.root, "TruthCore.Up.Solution"),
                         {"TruthCore.Base.Solution": 1, "TruthCore.Vocab": 1, "TruthCore.Deep.Solution": 2})
        self.assertEqual([b["name"] for b in theorem_blocks(self.root, "TruthCore.Base.Solution")], ["exported"])

    def test_proof_term_reuse_distinguishes_three_review_classes_without_changing_graph(self):
        write(self.root, "TruthCore.Up.Solution",
              "import TruthCore.Base.Solution\nimport TruthCore.Peer.Solution\nimport TruthCore.Vocab\n")
        before = (copy.deepcopy(self.data), copy.deepcopy(self.report))
        usage = {"Demo.Up.main": ["Demo.Base.main", "Demo.Peer.main"]}
        pack = context_pack(self.root, self.data, self.report, "UP", proof_uses=usage)
        lean = pack["lean"][0]
        reused = {r["result_id"]: r for r in lean["reused_results"]}
        self.assertEqual({rid: r["classification"] for rid, r in reused.items()}, {
            "BASE": "theorem-used, graph-linked",
            "PEER": "theorem-used, not in argument graph",
            "DEEP": "import only",
        })
        self.assertTrue(reused["BASE"]["graph_linked"])
        self.assertFalse(reused["PEER"]["graph_linked"])
        self.assertFalse(reused["DEEP"]["theorem_used"])
        self.assertIn("transcription", reused["BASE"])
        self.assertEqual(lean["proof_theorems"], ["Demo.Base.main", "Demo.Peer.main"])
        self.assertIn("theorem-used, not in argument graph", format_context(pack))
        report = lean_reuse_review(self.root, self.data["results"],
                                   {a["id"]: a for a in self.data["arguments"]}, usage)
        self.assertEqual(report["summary"], {
            "results_inspected": 1,
            "theorem-used, graph-linked": 1,
            "theorem-used, not in argument graph": 1,
            "import only": 1,
        })
        self.assertEqual(before, (self.data, self.report))
        self.assertNotIn("classification", self.pack()["lean"][0]["reused_results"][0])

    def test_proof_use_without_source_import_is_reported_not_discarded(self):
        usage = {"Demo.Up.main": ["Demo.Peer.main"]}
        lean = context_pack(self.root, self.data, self.report, "UP", proof_uses=usage)["lean"][0]
        peer = next(r for r in lean["reused_results"] if r["result_id"] == "PEER")
        self.assertEqual(peer["classification"], "theorem-used, not in argument graph")
        self.assertIsNone(peer["depth"])

    def test_lean_reuse_export_rejects_missing_and_malformed_proofs(self):
        theorem = "Demo.Up.main"
        with self.assertRaisesRegex(corpus.CorpusError, "did not inspect"):
            corpus.lean_reuse_usage_map([], [theorem])
        with self.assertRaisesRegex(corpus.CorpusError, "could not inspect"):
            corpus.lean_reuse_usage_map([{"theorem": theorem, "error": "unknown theorem"}], [theorem])
        with self.assertRaisesRegex(corpus.CorpusError, "proof_theorems"):
            corpus.lean_reuse_usage_map([{"theorem": theorem, "proof_theorems": None}], [theorem])
        self.assertEqual(corpus.lean_reuse_usage_map([
            {"theorem": theorem, "proof_theorems": ["Demo.Base.main", "Demo.Base.main"]},
        ], [theorem]), {theorem: ["Demo.Base.main"]})

    def test_lean_reuse_uses_built_tool_without_rebuilding_and_scopes_imports(self):
        records = [(self.root, result) for result in self.data["results"]]
        with patch.object(corpus, "run_bind_tool", return_value=[]) as runner:
            self.assertEqual(corpus.run_lean_reuse_tool(records, inspect=["Demo.Up.main"]), [])
        tool_input = runner.call_args.args[0]
        self.assertEqual(tool_input["modules"], ["TruthCore.Up.Solution"])
        self.assertEqual(tool_input["inspect"], ["Demo.Up.main"])
        self.assertIn("Demo.Peer.main", tool_input["theorems"])
        self.assertEqual(runner.call_args.kwargs["command_name"], "lean-reuse")

    def test_graph_neighbourhood_preserves_bundles_and_flags_duplicates(self):
        pack = self.pack()
        premises = {p["statement_id"]: p for p in pack["premises"]}
        self.assertEqual([c["argument_id"] for c in premises["P"]["concluded_by"]], ["BASE"])
        self.assertEqual(premises["P"]["concluded_by"][0]["premise_statement_ids"], ["X"])
        self.assertEqual([c["argument_id"] for c in pack["conclusion"]["concluded_by"]], ["TWIN"])
        self.assertEqual(pack["same_bundle_argument_ids"], ["TWIN"])
        self.assertEqual([d["argument_id"] for d in pack["downstream_arguments"]], ["DOWN"])

    def test_countermodels_attempts_and_candidates_are_scoped_to_the_argument(self):
        pack = self.pack()
        self.assertEqual([(m["statement_id"], m["value"]) for m in pack["models"]], [("Q", "violates"), ("P", "satisfies")])
        self.assertEqual([r["relation_id"] for r in pack["rival_relations"]], ["REL-ALT"])
        # Statement-linked or evidence-linked attempts only, newest first.
        self.assertEqual([a["attempt_id"] for a in pack["attempts"]], ["ATTEMPT-NEW", "ATTEMPT-OLD"])
        self.assertEqual(pack["unresolved"]["blocked_or_failed_attempt_ids"], ["ATTEMPT-OLD"])
        # Whole-token matching: "QX" and "STMT-Q" do not mention Q.
        self.assertEqual([(c["candidate_id"], c["mentions"]) for c in pack["candidates"]], [("CAND-Q", ["Q", "UP"])])
        self.assertEqual(pack["configurations"], [{"configuration_id": "CONFIG-C", "semantics_id": "sem", "statement_ids": ["C", "Q"]}])

    def test_open_premises_follow_the_frontier_report_and_nothing_is_mutated(self):
        before = (copy.deepcopy(self.data), copy.deepcopy(self.report))
        pack = self.pack()
        self.assertEqual(before, (self.data, self.report))
        self.assertEqual(pack["unresolved"]["open_premise_statement_ids"],
                         [sid for sid in ["P", "Q"] if not self.report["closed_statements"].get(sid)])
        self.assertNotIn("P", pack["unresolved"]["open_premises_without_other_route"])

    def test_text_is_bounded_and_names_every_section(self):
        text = format_context(self.pack(), limit=1)
        for heading in ("Conclusion C", "Premises (2", "Lean (authoritative", "theorem main {B : Type}",
                        "companion theorems", "Countermodels and rivals", "MODEL-M violates premise Q",
                        "Attempts on these statements", "Unresolved:", "DEF-C"):
            self.assertIn(heading, text)
        # A truncated section names its hidden entries by ID (#962).
        self.assertIn("… 1 more: ATTEMPT-OLD (see --json)", text)
        self.assertIn("… and whose Solution imports one of those: FAR", text)
        capped = format_context(self.pack(), limit=0, overflow=0)
        self.assertNotIn("ATTEMPT-OLD", capped.split("Candidates")[0].split("Attempts")[1])

    def test_neighbours_share_premises_or_vocabulary_imports_and_related_passes_through(self):
        pack = context_pack(self.root, self.data, self.report, "UP",
                            related=[{"statement_id": "X", "reasons": [{"kind": "argument"}, {"kind": "text"}]}])
        self.assertEqual([(d["argument_id"], d["shared_premise_statement_ids"]) for d in pack["premise_sibling_arguments"]],
                         [("TWIN", ["P", "Q"]), ("PEER", ["Q"])])
        # PEER shares the non-result vocabulary import; BASE is a reused result, not a neighbour.
        self.assertEqual([(n["result_id"], n["shared_modules"]) for n in pack["lean_neighbours"]], [("PEER", ["TruthCore.Vocab"])])
        self.assertEqual(pack["related_statements"], [{"statement_id": "X", "reasons": ["argument", "text"]}])

    def test_route_leaves_and_attempt_citations_are_ranked_id_lists(self):
        self.report["routes"]["routes"] = [
            {"argument_id": "R1", "cost": 2, "open_premise_statement_ids": ["P", "X"]},
            {"argument_id": "R2", "cost": 2, "open_premise_statement_ids": ["Q", "X", "D"]},
            {"argument_id": "R3", "cost": 1, "open_premise_statement_ids": ["D"]},  # touches nothing of ours
        ]
        self.data["attempts"][0]["summary"] = "Tried MODEL-M against ATTEMPT-NEW; NOT-AN-ID and bare DEEP stay out."
        self.data["attempts"][1]["evidence"] = ["UP", "MODEL-M"]
        pack = self.pack()
        self.assertEqual([r["argument_id"] for r in pack["routes"]], ["R1", "R2"])
        self.assertEqual(pack["route_open_leaves"], ["X", "D"])  # X on two routes, D on one; own premises excluded
        # Known IDs only, excluding the argument's own statements and results.
        self.assertEqual(pack["attempt_cited_ids"], ["MODEL-M"])
        text = format_context(pack)
        self.assertIn("other open leaves on these routes (most routes first): X, D", text)
        self.assertIn("IDs these attempts cite (most cited first; discovery only): MODEL-M", text)

    def test_target_resolution(self):
        arguments = {a["id"]: a for a in self.data["arguments"]}
        results = {r["id"]: r for r in self.data["results"]}
        self.assertEqual(resolve_target("UP", arguments, results), ("UP", []))
        self.assertEqual(resolve_target("D", arguments, results), ("DOWN", []))
        self.assertEqual(resolve_target("C", arguments, results), (None, ["TWIN", "UP"]))
        self.assertEqual(resolve_target("NOPE", arguments, results), (None, []))


class RepositoryContextTests(unittest.TestCase):
    def test_lean_reuse_exporter_reads_an_existing_compiled_result(self):
        if shutil.which("lake") is None:
            self.skipTest("Lean toolchain is not installed")
        results = corpus.load_dir("results")
        target = next(record for _, record in results
                      if record["id"] == "AQUINAS-ST-I-Q11-A3-GOD-ONE-FROM-NATURE")
        rows = corpus.run_lean_reuse_tool(results, inspect=[target["theorem"]])
        usage = corpus.lean_reuse_usage_map(rows, [target["theorem"]])
        self.assertIsInstance(usage[target["theorem"]], list)

    def test_existing_argument_pack_runs_on_the_real_corpus(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = corpus.main_with(["context", "--json", "AQUINAS-ST-I-Q11-A3-GOD-ONE-FROM-NATURE"])
        self.assertEqual(code, 0)
        pack = json.loads(out.getvalue())
        self.assertEqual(pack["conclusion"]["statement_id"], "STMT-GOD-IS-ONE")
        self.assertIn("theorem godIsOneFromNature", pack["lean"][0]["advertised_statement"]["statement"])


if __name__ == "__main__":
    unittest.main()
