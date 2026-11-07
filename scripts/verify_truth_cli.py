#!/usr/bin/env python3
"""Compare the Rust CLI with the existing Python corpus readers: the
structural view (`status`, `inspect`), `thickness [--queue]`, `frontier`
and `frontier-diff`."""
import argparse
import copy
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import corpus
import source_evidence


class TruthParity(unittest.TestCase):
    def invoke(self, *args, code=0):
        result = subprocess.run(
            [self.binary, "--json", *args], cwd=corpus.ROOT,
            capture_output=True, text=True, check=False,
        )
        self.assertEqual(result.returncode, code, result.stderr)
        return json.loads(result.stderr if code else result.stdout)

    def test_real_status_and_inspect(self):
        expected = corpus.validate()
        status = self.invoke("status")
        for kind, count in status["counts"].items():
            oracle = expected[kind] if kind in expected else len(corpus.load_dir(kind))
            self.assertEqual(count, oracle, kind)

        records = {}
        for kind in status["counts"]:
            entries = source_evidence.load_passages() if kind == "passages" else corpus.load_dir(kind)
            for path, record in entries:
                records.setdefault(record["id"], []).append({
                    "kind": kind, "path": path.relative_to(corpus.ROOT).as_posix(), "record": record,
                })
        # Cover every kind and a shared ID across kinds with bounded CLI invocations.
        ids = {next(key for key, entries in records.items()
                    if any(entry["kind"] == kind for entry in entries))
               for kind, count in status["counts"].items() if count}
        ids.add(next(key for key, entries in records.items() if len(entries) > 1))
        for key in sorted(ids):
            result = self.invoke("inspect", key)
            self.assertEqual(result["matches"], records[key])
            self.assertEqual(result["input_identity"], status["input_identity"])

    def test_errors_and_input_changes(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            directory = root / "corpus" / "statements"
            directory.mkdir(parents=True)
            path = directory / "a.json"
            args = ("--root", str(root))
            record = {"id": "STMT-FIXTURE", "paraphrase": "One"}
            path.write_text(json.dumps(record))
            first = self.invoke(*args, "status")["input_identity"]
            path.write_text(json.dumps({**record, "paraphrase": "Two"}))
            second = self.invoke(*args, "status")["input_identity"]
            self.assertNotEqual(first, second)
            self.assertEqual(self.invoke(*args, "inspect", "UNKNOWN", code=3)["error"]["code"],
                             "unknown_id")
            duplicate = directory / "z.json"
            duplicate.write_text(json.dumps(record))
            with self.assertRaisesRegex(corpus.CorpusError, "duplicate statement id"):
                corpus.index_by_id([(p, record) for p in (corpus.ROOT / "a.json", corpus.ROOT / "z.json")],
                                   "statement")
            error = self.invoke(*args, "status", code=1)["error"]
            self.assertEqual((error["code"], error["path"]),
                             ("duplicate_id", "corpus/statements/z.json"))
            duplicate.unlink()
            for value, error_code in [
                ("{", "invalid_json_object"), ("[]", "invalid_json_object"),
                ('{"id": 1}', "invalid_field"), ('{"id": "STMT-FIXTURE"}', "invalid_field"),
            ]:
                path.write_text(value)
                self.assertEqual(self.invoke(*args, "status", code=1)["error"]["code"], error_code)

    def test_symlinks_cannot_escape_the_corpus_boundary(self):
        with tempfile.TemporaryDirectory() as temporary, tempfile.TemporaryDirectory() as outside:
            root = Path(temporary)
            directory = root / "corpus" / "statements"
            directory.mkdir(parents=True)
            foreign = Path(outside) / "foreign.json"
            foreign.write_text(json.dumps({"id": "STMT-FOREIGN", "paraphrase": "Not in corpus"}))
            link = directory / "linked.json"
            link.symlink_to(foreign)
            result = self.invoke("--root", str(root), "status", code=1)
            self.assertEqual(result["error"]["code"], "invalid_path")
            self.assertEqual(result["error"]["path"], "corpus/statements/linked.json")
            link.unlink()
            directory.rmdir()
            directory.symlink_to(Path(outside), target_is_directory=True)
            result = self.invoke("--root", str(root), "status", code=1)
            self.assertEqual(result["error"]["code"], "invalid_path")
            # The corpus directory itself may not be a symlink either.
            directory.unlink()
            (Path(outside) / "statements").mkdir()
            (Path(outside) / "statements" / "foreign.json").write_text(foreign.read_text())
            (root / "corpus").rmdir()
            (root / "corpus").symlink_to(Path(outside), target_is_directory=True)
            result = self.invoke("--root", str(root), "status", code=1)
            self.assertEqual((result["error"]["code"], result["error"]["path"]), ("invalid_path", "corpus"))

    def test_bridges_contract(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "corpus" / "statements").mkdir(parents=True)
            for sid, decl in [("STMT-T", "N.T"), ("STMT-A", "N.A")]:
                (root / "corpus" / "statements" / f"{sid}.json").write_text(
                    json.dumps({"id": sid, "paraphrase": sid, "lean_declaration": decl}))
            constants = root / "constants.json"
            constants.write_text(json.dumps([
                {"declaration": "N.T", "constants": ["N.P", "N.T"]},
                {"declaration": "N.A", "constants": ["N.A", "N.P"]},
            ]))
            args = ("--root", str(root), "bridges", "--constants", str(constants))
            report = self.invoke(*args, "--target", "STMT-T")
            self.assertEqual(report["targets"][0]["singles"][0]["statement_ids"], ["STMT-A"])
            self.assertIn("NOT a proof", report["mode"])
            self.assertEqual(self.invoke(*args, code=2)["error"]["code"], "usage")
            self.assertEqual(self.invoke(*args, "--target", "STMT-X", code=3)["error"]["code"],
                             "unknown_id")
            self.assertEqual(self.invoke("--root", str(root), "status", "--top", "2", code=2)
                             ["error"]["code"], "usage")

    def test_non_utf8_root_path_is_accepted(self):
        import os

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(os.fsdecode(os.fsencode(temporary) + b"/root-\xff"))
            (root / "corpus" / "statements").mkdir(parents=True)
            (root / "corpus" / "statements" / "a.json").write_text(
                json.dumps({"id": "STMT-FIXTURE", "paraphrase": "One"})
            )
            result = subprocess.run(
                [self.binary, "--json", "--root", os.fsencode(str(root)), "status"],
                capture_output=True, check=False,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(result.stdout)["counts"]["statements"], 1)


def thickness_fixture(root):
    """A small corpus covering AND premises, a root_route, a strength
    registration, a counted refutation, a heuristic (Lean-text) and a declared
    transcription, source depths, attempts and a definition-linked candidate."""
    def write(kind, record):
        directory = root / "corpus" / kind
        directory.mkdir(parents=True, exist_ok=True)
        (directory / f"{record['id']}.json").write_text(json.dumps(record))

    for statement_id in ["ROOT", "A", "B", "C", "D", "E", "W", "S", "R", "X", "U"]:
        definitions = ["DEF-T"] if statement_id in {"C", "U"} else []
        write("statements", {"id": statement_id, "paraphrase": statement_id,
                             "definition_ids": definitions,
                             **({"lean_declaration": f"Fixture.{statement_id}"} if statement_id == "A" else {})})
    for argument_id, premises, conclusion in [
        ("ARG-ROOT", ["A", "B"], "ROOT"), ("ARG-ROOT-UNROUTED", ["E"], "ROOT"),
        ("ARG-A", ["C"], "A"), ("ARG-A-T", ["D"], "A"), ("ARG-B", ["W"], "B"),
        ("ARG-B-H", ["A"], "B"), ("ARG-STRENGTH", ["S"], "W"), ("ARG-REFUTE-R", [], "X"),
    ]:
        write("arguments", {"id": argument_id, "premise_statement_ids": premises,
                            "conclusion_statement_id": conclusion, "inference_ids": ["INF"],
                            "meaning": argument_id})
    (root / "Fixture").mkdir()
    (root / "Fixture" / "Solution.lean").write_text(
        "theorem b_from_a (A B : Prop) (h : A → B) (a : A) : B := by\n  exact h a\n"
    )
    for result_id, argument_id, extra in [
        ("RES-ROOT", "ARG-ROOT", {}), ("RES-ROOT-UNROUTED", "ARG-ROOT-UNROUTED", {}),
        ("RES-A", "ARG-A", {}), ("RES-A-T", "ARG-A-T", {"transcription": "assembly"}),
        ("RES-B-H", "ARG-B-H", {"theorem": "Fixture.b_from_a"}),
        ("RES-STRENGTH", "ARG-STRENGTH", {}), ("RES-REFUTE", "ARG-REFUTE-R", {}),
    ]:
        write("results", {"id": result_id, "argument_id": argument_id, "challenge_module": "Fixture.Challenge",
                          "solution_module": "Fixture.Solution", "theorem": "Fixture.none",
                          "comparator_config": "c.json", "status": "verified", **extra})
    for relation_id, subject_kind, subject, predicate, obj, extra in [
        ("REL-ROUTE", "argument", "ARG-ROOT", "root_route", "ROOT", {}),
        ("REL-STRENGTH", "statement", "S", "strengthens", "W", {"verification_result_id": "RES-STRENGTH"}),
        ("REL-ALT", "statement", "R", "alternative_to", "C", {}),
        ("REL-REFUTE", "argument", "ARG-REFUTE-R", "refutes", "R", {}),
        ("REL-SUPPORT", "claim", "CLAIM-B", "supports", "B", {}),
    ]:
        write("relations", {"id": relation_id, "subject_kind": subject_kind, "subject_id": subject,
                            "predicate": predicate, "object_kind": "statement", "object_id": obj, **extra})
    for claim_id, statement_id, extra in [
        ("CLAIM-D", "D", {}), ("CLAIM-E", "E", {"witness": "bibliographic"}), ("CLAIM-U", "U", {}),
    ]:
        write("claims", {"id": claim_id, "statement_id": statement_id, "source_id": "SRC", "locator": "1",
                         "interpretation": "i", "status": "accepted", **extra})
    write("definitions", {"id": "DEF-T", "term": "t", "definition": "t", "basis": "stipulative",
                          "claim_ids": ["CLAIM-U"]})
    for attempt_id, outcome, statements in [("ATT-2", "inconclusive", ["W"]), ("ATT-1", "rejected", ["W"])]:
        write("attempts", {"id": attempt_id, "outcome": outcome, "statement_ids": statements})


def python_thickness(root, queue):
    """Python `thickness [--queue] --json` on a fixture checkout, without the
    full `validate()` the command runs first."""
    records = {kind: [json.loads(path.read_text()) for path in sorted((root / "corpus" / kind).glob("*.json"))]
               for kind in ("statements", "arguments", "results", "relations", "attempts", "definitions", "claims")}
    saved = corpus.ROOT
    corpus.ROOT = root
    try:
        flags = corpus.transcription_flags(records["results"], records["arguments"], records["statements"])
    finally:
        corpus.ROOT = saved
    frontier = corpus.frontier_report(records["statements"], records["arguments"], records["results"],
                                      records["relations"], root="ROOT", transcription=flags, claims=records["claims"])
    report = corpus.thickness_report(frontier, records["arguments"], records["results"])
    if queue:
        return {"root": "ROOT", "queue": corpus.thickness_queue(frontier, report, records)}
    return {"report": report, "delta": None}


class TruthThicknessParity(unittest.TestCase):
    """`truth thickness [--queue]` against `corpus.py thickness [--queue]`."""

    def run_truth(self, *args):
        result = subprocess.run([self.binary, *args], cwd=corpus.ROOT,
                                capture_output=True, text=True, check=False)
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout

    def test_real_corpus(self):
        # The functions `corpus.py thickness [--queue] [--json]` prints, on one frontier.
        frontier = corpus.current_frontier(corpus.DEFAULT_FRONTIER_ROOT, False, next_steps=False)
        records = {kind: [record for _, record in corpus.load_dir(kind)]
                   for kind in ("statements", "arguments", "results", "relations", "attempts", "definitions",
                                "claims")}
        report = corpus.thickness_report(frontier, records["arguments"], records["results"])
        queue = corpus.thickness_queue(frontier, report, records)
        root = report["root"]
        for flags, expected, text in (
            ([], {"report": report, "delta": None}, corpus.format_thickness(report, None)),
            (["--queue"], {"root": root, "queue": queue}, corpus.format_thickness_queue(root, queue)),
        ):
            actual = json.loads(self.run_truth("--json", "thickness", *flags))
            self.assertTrue(actual.pop("input_identity").startswith("fnv1a64:"))
            self.assertEqual(actual, expected, flags)
            self.assertEqual(self.run_truth("thickness", *flags), text + "\n", flags)

    def test_fixture(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            thickness_fixture(root)
            for flags, queue in (([], False), (["--queue"], True)):
                actual = json.loads(self.run_truth("--json", "--root", str(root), "--frontier-root", "ROOT",
                                                   "thickness", *flags))
                actual.pop("input_identity")
                self.assertEqual(actual, python_thickness(root, queue), flags)
            report = python_thickness(root, False)["report"]
            # The heuristic transcription (RES-B-H) derives nothing; B is queued.
            self.assertEqual(report["derivations"]["B"], [])
            self.assertEqual(report["derivations"]["A"], ["ARG-A"])

    def test_usage(self):
        result = subprocess.run([self.binary, "--json", "--queue", "status"], cwd=corpus.ROOT,
                                capture_output=True, text=True, check=False)
        self.assertEqual(result.returncode, 2)


def frontier_fixture(root):
    """The thickness fixture plus floor markings of every basis (met, unmet,
    owner-approved), a counted retorsion, an unrefuted sceptical rival, an
    objection, inferences and stages, a transcription closure, unavailable and
    bibliographic witnesses, a case split, settlement actions and a Lean
    definition behind the goal-consequent and opaque-atom heuristics."""
    thickness_fixture(root)

    def write(kind, record):
        (root / "corpus" / kind / f"{record['id']}.json").write_text(json.dumps(record))

    (root / "corpus" / "inferences").mkdir(exist_ok=True)
    statements = {
        "F-LEG": {"self_evident": {"basis": None}},
        "F-RET": {"self_evident": {"basis": "retorsion", "denial_statement_id": "NF",
                                   "justification_ids": ["RES-RET"]}},
        "F-OBS": {"self_evident": {"basis": "observation", "justification_ids": ["CLAIM-OBS"],
                                   "sceptical_rival_ids": ["SK"]}},
        "F-CG": {"self_evident": {"basis": "common_ground", "question_statement_id": "Q",
                                  "positions": [{"statement_id": "Q", "claim_ids": ["CLAIM-CG"]}]}},
        "F-OWN": {"self_evident": {"basis": "common_ground", "question_statement_id": "Q",
                                   "owner_approval": {"decision": "https://example.invalid/1"},
                                   "disagreement": {"rival_statement_ids": ["Q2"]}}},
        "F-STALE": {"self_evident": {"basis": "legacy", "owner_approval": {"decision": "https://example.invalid/2"},
                                     "disagreement": {"rival_statement_ids": []}}},
        "NF": {}, "SK": {}, "Q": {}, "Q2": {}, "TC": {}, "BR": {"lean_declaration": "Fixture.Bridge"},
        "OPQ": {}, "STMT-GOD-EXISTS": {},
    }
    for statement_id, extra in statements.items():
        write("statements", {"id": statement_id, "paraphrase": f"{statement_id} paraphrase", **extra})
    e = json.loads((root / "corpus" / "statements" / "E.json").read_text())
    e["settlement_actions"] = [{"kind": "floor", "status": "needs-owner-decision", "description": "d"}]
    write("statements", e)
    for argument_id, premises, conclusion in [
        ("ARG-RET", [], "X"), ("ARG-USE", ["F-LEG", "F-RET", "F-OBS", "F-CG", "F-OWN"], "C"),
        ("ARG-TC", ["F-LEG"], "TC"), ("ARG-TC-USE", ["TC", "OPQ"], "E"), ("ARG-OPQ", ["BR", "D"], "OPQ"),
        ("ARG-GOD", ["U"], "STMT-GOD-EXISTS"),
    ]:
        write("arguments", {"id": argument_id, "premise_statement_ids": premises,
                            "conclusion_statement_id": conclusion, "inference_ids": ["INF"],
                            "meaning": argument_id})
    write("inferences", {"id": "INF", "output_statement_id": "U", "input_statement_ids": ["D"],
                         "assumption_statement_ids": ["Q2"], "discharged_statement_ids": [],
                         "rule": "r", "meaning": "m"})
    (root / "TruthCore").mkdir()
    (root / "TruthCore" / "Defs.lean").write_text("def Bridge (P Q : Prop) : Prop := P → Q\n")
    (root / "Fixture" / "Opaque.lean").write_text(
        "theorem opaque_step (A B : Prop) (h : Bridge A B) (a : A) : B := by\n"
        "  have x := h a\n  exact x\n  done\n"
    )
    for result_id, argument_id, extra in [
        ("RES-RET", "ARG-RET", {}), ("RES-USE", "ARG-USE", {}),
        ("RES-TC", "ARG-TC", {"transcription": "single_application"}),
        ("RES-OPQ", "ARG-OPQ", {"solution_module": "Fixture.Opaque", "theorem": "Fixture.opaque_step"}),
        ("RES-GOD", "ARG-GOD", {"joint_settlement_schema": True,
                                "case_split": {"target_statement_id": "ROOT", "note": "n", "cases": [
                                    {"label": "one", "lean_declaration": "TruthCore.One", "statement_id": "R"},
                                    {"label": "two", "lean_declaration": "TruthCore.Two"}]}}),
    ]:
        write("results", {"id": result_id, "argument_id": argument_id, "challenge_module": "Fixture.Challenge",
                          "solution_module": "Fixture.Solution", "theorem": "Fixture.none",
                          "comparator_config": "c.json", "status": "verified", **extra})
    for relation_id, subject_kind, subject, predicate, obj in [
        ("REL-ALT-NF", "statement", "NF", "alternative_to", "F-RET"),
        ("REL-REFUTE-NF", "argument", "ARG-RET", "refutes", "NF"),
        ("REL-ALT-SK", "statement", "SK", "alternative_to", "F-OBS"),
        ("REL-ALT-Q", "statement", "Q2", "alternative_to", "Q"),
        ("REL-ALT-OWN", "statement", "Q2", "alternative_to", "F-OWN"),
        ("REL-ALT-STALE", "statement", "Q2", "alternative_to", "F-STALE"),
        ("REL-ATTACK", "statement", "Q2", "attacks", "D"),
        ("REL-REFUTE-OPEN", "argument", "ARG-B-H", "refutes", "Q2"),
    ]:
        write("relations", {"id": relation_id, "subject_kind": subject_kind, "subject_id": subject,
                            "predicate": predicate, "object_kind": "statement", "object_id": obj})
    for claim_id, statement_id, extra in [
        ("CLAIM-OBS", "F-OBS", {}), ("CLAIM-CG", "F-CG", {}),
        ("CLAIM-BR", "BR", {"witness": "unavailable"}), ("CLAIM-D2", "D", {"witness": "bibliographic"}),
    ]:
        write("claims", {"id": claim_id, "statement_id": statement_id, "source_id": "SRC", "locator": "1",
                         "interpretation": "i", "status": "accepted", **extra})


def python_frontier(root, frontier_root="ROOT"):
    """Python `frontier_report` with next steps on a fixture checkout, without
    the full `validate()` that `corpus.py frontier` runs first."""
    kinds = ("statements", "arguments", "results", "relations", "claims", "inferences")
    records = {kind: [json.loads(path.read_text()) for path in sorted((root / "corpus" / kind).glob("*.json"))]
               for kind in kinds}
    saved = corpus.ROOT
    corpus.ROOT = root
    try:
        flags = corpus.transcription_flags(records["results"], records["arguments"], records["statements"])
    finally:
        corpus.ROOT = saved
    return corpus.frontier_report(records["statements"], records["arguments"], records["results"],
                                  records["relations"], root=frontier_root, transcription=flags,
                                  claims=records["claims"], inferences=records["inferences"],
                                  _include_next_steps=True)


class TruthFrontierParity(unittest.TestCase):
    """`truth frontier` and `frontier-diff` against `corpus.py`."""

    def run_truth(self, *args):
        result = subprocess.run([self.binary, *args], cwd=corpus.ROOT,
                                capture_output=True, text=True, check=False)
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout

    def json_truth(self, *args):
        actual = json.loads(self.run_truth("--json", *args))
        self.assertTrue(actual.pop("input_identity").startswith("fnv1a64:"))
        return actual

    def assert_frontier(self, full, args):
        """Every `frontier` form against one Python report with next steps."""
        restricted = corpus.restrict_to_root(copy.deepcopy(full))
        for flags, report in (([], full), (["--reaching-root"], restricted)):
            self.assertEqual(self.json_truth(*args, "frontier", *flags), report, flags)
            without = {key: value for key, value in report.items() if key != "next_steps"}
            self.assertEqual(self.run_truth(*args, "frontier", *flags), corpus.format_frontier(without) + "\n")
            self.assertEqual(self.json_truth(*args, "frontier", "--routes", *flags), report["routes"], flags)
            self.assertEqual(self.run_truth(*args, "frontier", "--routes", *flags),
                             corpus.format_routes(report["routes"]) + "\n", flags)

    def test_real_corpus(self):
        root = corpus.DEFAULT_FRONTIER_ROOT
        self.assert_frontier(corpus.current_frontier(root, False), [])

    def test_real_frontier_diff(self):
        # Base HEAD: the Rust engine when HEAD's corpus.py is the checkout's.
        root = corpus.DEFAULT_FRONTIER_ROOT
        head = corpus.current_frontier(root, True, next_steps=False)
        delta = corpus.frontier_delta(corpus.revision_frontier("HEAD", root), head)
        delta.update(base="HEAD", head="working tree")
        actual = self.json_truth("frontier-diff", "--base", "HEAD")
        engines = actual.pop("engines")
        self.assertEqual(engines["head"], "rust")
        self.assertIn(engines["base"], {"rust", "python"})
        self.assertEqual(actual, delta)
        self.assertEqual(self.run_truth("frontier-diff", "--base", "HEAD"),
                         corpus.format_frontier_delta(delta) + "\n")

    def test_fixture(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            frontier_fixture(root)
            full = python_frontier(root)
            self.assert_frontier(full, ["--root", str(root), "--frontier-root", "ROOT"])
            # The fixture exercises what it claims to.
            self.assertEqual({entry["statement_id"]: entry["met"] for entry in full["floor"]},
                             {"F-LEG": True, "F-RET": True, "F-OBS": False, "F-CG": False, "F-OWN": True,
                              "F-STALE": False})
            self.assertEqual([c["statement_id"] for c in full["closed_via_transcription"]], ["B", "TC"])
            flags = {flag["result_id"]: flag for flag in full["transcription_flags"]}
            self.assertTrue(flags["RES-OPQ"]["opaque_atoms"])
            self.assertEqual(flags["RES-OPQ"]["goal_consequent_premises"],
                             [{"hypothesis": "h", "statement_ids": ["BR"]}])
            self.assertTrue(full["next_steps"]["partitions"])
            unknown = python_frontier(root, "NOT-A-STATEMENT")
            unknown_args = ["--root", str(root), "--frontier-root", "NOT-A-STATEMENT"]
            self.assertEqual(self.json_truth(*unknown_args, "frontier"), unknown)

    def test_usage(self):
        for args in (["frontier", "--queue"], ["frontier-diff"], ["status", "--routes"],
                     ["frontier", "--base", "HEAD"]):
            result = subprocess.run([self.binary, "--json", *args], cwd=corpus.ROOT,
                                    capture_output=True, text=True, check=False)
            self.assertEqual(result.returncode, 2, args)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=lambda path: Path(path).resolve())
    TruthParity.binary = TruthThicknessParity.binary = TruthFrontierParity.binary = parser.parse_args().binary
    unittest.main(argv=[__file__])
