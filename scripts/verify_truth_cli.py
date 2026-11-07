#!/usr/bin/env python3
"""Compare the Rust CLI with the existing Python corpus readers: the
structural view (`status`, `inspect`), `thickness [--queue]`, `check`,
`frontier`, `frontier-diff` and the research navigation commands `related`,
`dossier` and `context`."""
import argparse
import contextlib
import copy
import io
import json
import shutil
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
def spread(items, count):
    """`count` entries evenly spaced over a sorted list (deterministic sample)."""
    items = sorted(items)
    if len(items) <= count:
        return items
    return [items[index * len(items) // count] for index in range(count)]


class TruthResearchParity(unittest.TestCase):
    """`truth related|dossier|context` against `corpus.py related|dossier|context`
    on a broad real-corpus sample, one frontier report shared by both sides."""

    @classmethod
    def setUpClass(cls):
        from premise_dossiers import dossier_index

        directories = ("statements", "claims", "definitions", "disambiguations", "inferences", "arguments",
                       "results", "relations", "attempts", "models", "configurations", "candidates")
        cls.data = {name: [record for _, record in corpus.load_dir(name)] for name in directories}
        data = cls.data
        # The report `corpus.py dossier` and `context` compute, handed to Rust as a file.
        cls.report = corpus.frontier_report(
            data["statements"], data["arguments"], data["results"], data["relations"],
            root=corpus.DEFAULT_FRONTIER_ROOT,
            transcription=corpus.transcription_flags(data["results"], data["arguments"], data["statements"]),
            claims=data["claims"])
        cls.temporary = tempfile.TemporaryDirectory()
        cls.frontier = str(Path(cls.temporary.name) / "frontier.json")
        Path(cls.frontier).write_text(json.dumps(cls.report, ensure_ascii=False))
        cls.dossiers = dossier_index(data, cls.report)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def truth(self, *args, code=0):
        result = subprocess.run([self.binary, *args], cwd=corpus.ROOT,
                                capture_output=True, text=True, check=False)
        self.assertEqual(result.returncode, code, (args, result.stderr))
        return result.stdout, result.stderr

    def truth_json(self, *args):
        value = json.loads(self.truth("--json", *args)[0])
        self.assertTrue(value.pop("input_identity").startswith("fnv1a64:"))
        return value

    def statement_sample(self):
        report = self.report
        closed = list(report["closed_statements"])
        by_depth = {}
        for item in report["items"]:
            by_depth.setdefault(item["depth"], []).append(item["statement_id"])
        listed = set(closed) | {item["statement_id"] for item in report["items"]}
        others = [entry["id"] for entry in self.data["statements"] if entry["id"] not in listed]
        sample = set(spread(closed, 6)) | set(spread(others, 6))
        for depth in ("stated", "supported", "bare"):
            sample |= set(spread(by_depth.get(depth, []), 6))
        sample |= set(spread([entry["statement_id"] for entry in report["floor"]], 3))
        return sorted(sample)

    def test_related(self):
        for sid in self.statement_sample()[:30]:
            for limit in ("10", "3"):
                expected = io.StringIO()
                with contextlib.redirect_stdout(expected):
                    corpus.main_with(["related", sid, "--limit", limit])
                self.assertEqual(self.truth("related", sid, "--limit", limit)[0], expected.getvalue(), sid)
            from research_index import cached_related
            self.assertEqual(self.truth_json("related", sid), cached_related(corpus.ROOT, sid, 10), sid)
        self.assertEqual(json.loads(self.truth("--json", "related", "STMT-NO-SUCH", code=3)[1])["error"]["code"],
                         "unknown_id")
        argument = self.data["arguments"][0]["id"]
        self.assertIn("related requires a statement ID",
                      self.truth("related", f"arguments:{argument}", code=2)[1])

    def test_dossier(self):
        from premise_dossiers import format_dossier

        sample = self.statement_sample()
        self.assertGreaterEqual(len(sample), 30)
        for sid in sample:
            dossier = self.dossiers[sid]
            self.assertEqual(self.truth_json("dossier", sid, "--frontier-json", self.frontier), dossier, sid)
            for limit in (8, 0, 2):
                expected = format_dossier(dossier, self.data, limit=None if limit <= 0 else limit)
                actual = self.truth("dossier", sid, "--frontier-json", self.frontier, "--limit", str(limit))[0]
                self.assertEqual(actual, expected + "\n", (sid, limit))
        everything = json.loads(self.truth("dossier", "--all", "--frontier-json", self.frontier)[0])
        self.assertEqual(everything, self.dossiers)
        self.assertEqual(json.loads(self.truth("--json", "dossier", "STMT-NO-SUCH", "--frontier-json",
                                               self.frontier, code=3)[1])["error"]["code"], "unknown_id")
        # Without --frontier-json the Rust frontier computes the same report in-process.
        for sid in sample[:8]:
            self.assertEqual(self.truth_json("dossier", sid), self.dossiers[sid], sid)
            self.assertEqual(self.truth("dossier", sid)[0],
                             self.truth("dossier", sid, "--frontier-json", self.frontier)[0], sid)
        self.assertEqual(json.loads(self.truth("dossier", "--all")[0]), self.dossiers)
        self.assertEqual(json.loads(self.truth("--json", "dossier", sample[0], "--frontier-root", "STMT-NO-SUCH",
                                               code=1)[1])["error"]["message"],
                         "unknown root statement: STMT-NO-SUCH")

    def test_context(self):
        from argument_context import context_pack, format_context, resolve_target
        from research_index import cached_related

        arguments = {entry["id"]: entry for entry in self.data["arguments"]}
        results = {entry["id"]: entry for entry in self.data["results"]}
        concluded = {}
        for entry in self.data["arguments"]:
            concluded.setdefault(entry["conclusion_statement_id"], []).append(entry["id"])
        unique = [sid for sid, ids in concluded.items() if len(ids) == 1 and sid not in arguments]
        targets = (spread(arguments, 12) + spread([rid for rid in results if rid not in arguments], 3)
                   + spread(unique, 3))
        self.assertGreaterEqual(len(targets), 15)
        for target in targets:
            argument_id, _ = resolve_target(target, arguments, results)
            related = cached_related(corpus.ROOT, arguments[argument_id]["conclusion_statement_id"], 8)["matches"]
            pack = context_pack(corpus.ROOT, self.data, self.report, argument_id, related=related)
            self.assertEqual(self.truth_json("context", target, "--frontier-json", self.frontier), pack, target)
            for limit in (6, 2, -1):
                actual = self.truth("context", target, "--frontier-json", self.frontier, "--limit", str(limit))[0]
                self.assertEqual(actual, format_context(pack, limit=limit) + "\n", (target, limit))
        for target in targets[:5]:
            self.assertEqual(self.truth_json("context", target),
                             self.truth_json("context", target, "--frontier-json", self.frontier), target)
            self.assertEqual(self.truth("context", target)[0],
                             self.truth("context", target, "--frontier-json", self.frontier)[0], target)
        no_related = self.truth_json("context", targets[0], "--frontier-json", self.frontier, "--related", "0")
        self.assertEqual(no_related["related_statements"], [])
        self.assertEqual(json.loads(self.truth("--json", "context", "NO-SUCH-TARGET", "--frontier-json",
                                               self.frontier, code=3)[1])["error"]["code"], "unknown_id")
        several = next(sid for sid, ids in concluded.items() if len(ids) > 1)
        self.assertIn("is concluded by several arguments",
                      self.truth("context", several, "--frontier-json", self.frontier, code=2)[1])


# --- `truth check` against `corpus.py check` --------------------------------

REVISION = "0" * 40
CHECK_LEAN = {
    "TruthCore/Fix/Challenge.lean": "theorem fixAB (h : fixA) : fixB := sorry\n",
    "TruthCore/Fix/Solution.lean": (
        "def fixA : Prop := True\ndef fixB : Prop := True\ndef fixC : Prop := True\n"
        "def fixD : Prop := True\ndef fixE : Prop := True\n"
        "theorem fixAB (h : fixA) : fixB := trivial\ntheorem fixBC (h : fixB) : fixC := trivial\n"
        "def markConcrete (_ : Nat) : Prop := True\n"
        "-- category-constant: intended (the fixture's point)\ndef markAbstract (_ : Nat) : Prop := False\n"
    ),
}


def check_records():
    """A small corpus that passes `corpus.py check` with one warning of each
    ported kind: an unverified refutation, a supports relation without a
    note, a strong version used without `strong_version_needed`, a constant
    category predicate and an unmet floor basis."""
    def statement(sid, decl, **extra):
        return {"id": sid, "paraphrase": sid, "lean_declaration": f"TruthCore.Fix.{decl}", **extra}

    def result(rid, argument, theorem):
        return {"id": rid, "argument_id": argument, "challenge_module": "TruthCore.Fix.Challenge",
                "solution_module": "TruthCore.Fix.Solution", "theorem": f"TruthCore.Fix.{theorem}",
                "comparator_config": f"results/{rid}/comparator.json", "status": "verified"}

    def relation(rid, sk, subject, predicate, obj, **extra):
        return {"id": rid, "subject_kind": sk, "subject_id": subject, "predicate": predicate,
                "object_kind": "statement", "object_id": obj, **extra}

    return {
        "sources": [{"id": "SRC", "kind": "text", "author": "A", "work": "W", "citation_system": "n",
                     "work_urn": "urn:cts:fix:w", "catalog_url": "https://example.org",
                     "edition_urns": ["urn:cts:fix:w.a", "urn:cts:fix:w.b"]}],
        "passages": [{"snapshot": {
            "source_id": "SRC", "edition_urn": "urn:cts:fix:w.a", "language": "la", "repository": "org/repo",
            "revision": REVISION, "path": "w.xml", "git_blob_sha": REVISION,
            "source_url": f"https://raw.githubusercontent.com/org/repo/{REVISION}/w.xml", "license": "PD"},
            "passages": [{"id": "P-1", "locator": "1", "claim_locator_prefixes": ["1"]}]}],
        "statements": [
            statement("STMT-A", "fixA"), statement("STMT-B", "fixB", definition_ids=["DEF-X"]),
            statement("STMT-C", "fixC", definition_ids=["DEF-Y"]), statement("STMT-D", "fixD"),
            statement("STMT-E", "fixE", self_evident={"justification_ids": ["CLAIM-A"], "basis": "observation",
                                                      "disagreement": "none recorded"}),
        ],
        "claims": [{"id": "CLAIM-A", "statement_id": "STMT-A", "source_id": "SRC", "locator": "1.1",
                    "interpretation": "i", "status": "formalized"}],
        "definitions": [
            {"id": "DEF-X", "term": "t", "definition": "first sense", "basis": "sourced", "claim_ids": ["CLAIM-A"]},
            {"id": "DEF-Y", "term": "t", "definition": "second sense", "basis": "stipulative", "note": "why"},
        ],
        "disambiguations": [{"id": "DISAMB-T", "term": "t", "resolution": "DEF-X here, DEF-Y there",
                             "sense_definition_ids": ["DEF-X", "DEF-Y"]}],
        "inferences": [
            {"id": f"INF-{a}{b}", "input_statement_ids": [f"STMT-{a}"], "assumption_statement_ids": [],
             "discharged_statement_ids": [], "output_statement_id": f"STMT-{b}", "rule": "mp", "meaning": "m"}
            for a, b in (("A", "B"), ("B", "C"), ("A", "D"))
        ],
        "arguments": [
            {"id": "ARG-AB", "premise_statement_ids": ["STMT-A"], "inference_ids": ["INF-AB"],
             "conclusion_statement_id": "STMT-B", "meaning": "m"},
            {"id": "ARG-BC", "premise_statement_ids": ["STMT-B"], "inference_ids": ["INF-BC"],
             "conclusion_statement_id": "STMT-C", "meaning": "m", "disambiguation_ids": ["DISAMB-T"]},
            {"id": "ARG-AD", "premise_statement_ids": ["STMT-A"], "inference_ids": ["INF-AD"],
             "conclusion_statement_id": "STMT-D", "meaning": "m"},
        ],
        "results": [result("RES-AB", "ARG-AB", "fixAB"), result("RES-BC", "ARG-BC", "fixBC")],
        "relations": [
            relation("REL-STR", "statement", "STMT-A", "strengthens", "STMT-B",
                     verification_result_id="RES-AB", note="A is the strong version"),
            relation("REL-SUP", "claim", "CLAIM-A", "supports", "STMT-C"),
            relation("REL-ALT", "statement", "STMT-E", "alternative_to", "STMT-C"),
            relation("REL-REF", "argument", "ARG-AD", "refutes", "STMT-E"),
        ],
        "candidates": [{"id": "CAND-1", "source_id": "SRC", "locator": "2", "priority": 1, "goal": "g",
                        "reason": "r", "status": "candidate"}],
        "attempts": [{"id": "ATTEMPT-ONE", "statement_ids": ["STMT-A"], "date": "2026-11-07",
                      "kind": "derivation", "outcome": "succeeded", "summary": "Derived STMT-B.",
                      "evidence": ["RES-AB", "PR-1"]}],
        "models": [{"id": "MODEL-FIX", "description": "d", "vocabulary": "fix",
                    "lean_declaration": "TruthCore.Fix.model", "modules": ["TruthCore.Fix.Solution"],
                    "bindings": {"W": "Bool"},
                    "carriers": [{"binding": "W", "theorem": "TruthCore.Fix.enum", "elements": ["true", "false"]}],
                    "evaluations": [{"statement_id": "STMT-A", "value": "satisfies",
                                     "theorem": "TruthCore.Fix.eval", "arguments": ["W"]}]}],
        "configurations": [{"id": "CONFIG-FIX", "seed_statement_id": "STMT-A",
                            "semantics": {"id": "p", "logic": "l", "frame": "f", "domain": "d", "identity": "i",
                                          "vocabulary": "fix", "parameters": [{"name": "W", "type": "Type"}],
                                          "applications": {"STMT-A": ["W"]},
                                          "modules": ["TruthCore.Fix.Solution"], "permitted_axioms": []},
                            "configurations": [{"id": "base", "statement_ids": ["STMT-A"]}],
                            "incompatibility_result_ids": [],
                            "model_bindings": [{"model_id": "MODEL-FIX", "parameters": {"W": "W"}}]}],
    }


def by_id(records, kind, rid):
    return next(record for record in records[kind] if record.get("id") == rid)


def mutate(kind, rid, **changes):
    def apply(records):
        record = by_id(records, kind, rid)
        for key, value in changes.items():
            if value is None:
                record.pop(key, None)
            else:
                record[key] = value
    return apply


def add(kind, record):
    return lambda records: records[kind].append(record)


def comparator(change):
    def apply(records, configs):
        change(configs["RES-AB"])
    return apply


# One deliberately broken corpus per rule; both implementations must report
# the same first error.
CHECK_FAILURES = {
    "duplicate id": add("statements", {"id": "STMT-A", "paraphrase": "again"}),
    "unknown claim statement reference": mutate("claims", "CLAIM-A", statement_id="STMT-NOPE"),
    "unknown inference reference": mutate("arguments", "ARG-AB", inference_ids=["INF-NOPE"]),
    "argument not grounded": mutate("arguments", "ARG-BC", inference_ids=["INF-AB"]),
    "missing disambiguation link for two senses": mutate("arguments", "ARG-BC", disambiguation_ids=None),
    "empty disambiguation_ids": mutate("statements", "STMT-C", disambiguation_ids=[]),
    "unknown definition link": mutate("statements", "STMT-C", definition_ids=["DEF-NOPE"]),
    "disambiguation with one sense": mutate("disambiguations", "DISAMB-T", sense_definition_ids=["DEF-X", "DEF-X"]),
    "unused definition": add("definitions", {"id": "DEF-Z", "term": "z", "definition": "z", "basis": "stipulative",
                                             "note": "n"}),
    "stipulative definition without note": mutate("definitions", "DEF-Y", note=None),
    "prose cites unknown id": mutate("disambiguations", "DISAMB-T", resolution="see STMT-GHOST"),
    "bad strengthens registration": mutate("relations", "REL-STR", verification_result_id="RES-BC"),
    "strengthens without note": mutate("relations", "REL-STR", note=" "),
    "duplicate strength registration": add("relations", {"id": "REL-STR-DUP", "subject_kind": "statement",
                                                         "subject_id": "STMT-A", "predicate": "strengthens",
                                                         "object_kind": "statement", "object_id": "STMT-B",
                                                         "verification_result_id": "RES-AB", "note": "n"}),
    "strong_version_needed names a non-premise": mutate("arguments", "ARG-BC",
                                                        strong_version_needed={"STMT-A": "why"}),
    "unknown attempt outcome": mutate("attempts", "ATTEMPT-ONE", outcome="maybe"),
    "attempt date not ISO": mutate("attempts", "ATTEMPT-ONE", date="2026-02-30"),
    "attempt evidence unknown": mutate("attempts", "ATTEMPT-ONE", evidence=["PR-0"]),
    "blocked attempt without blocker": mutate("attempts", "ATTEMPT-ONE", outcome="blocked"),
    "self_evident without basis": mutate("statements", "STMT-E", self_evident={"justification_ids": ["CLAIM-A"]}),
    "self_evident unknown rival": mutate("statements", "STMT-E", self_evident={
        "justification_ids": ["CLAIM-A"], "basis": "observation",
        "disagreement": {"rival_statement_ids": ["STMT-NOPE"]}}),
    "owner approval with a bad URL": mutate("statements", "STMT-E", self_evident={
        "justification_ids": ["CLAIM-A"], "basis": "observation", "disagreement": "none recorded",
        "owner_approval": {"decision": "https://example.org", "date": "2026-11-05"}}),
    "relation kind mismatch": mutate("relations", "REL-SUP", subject_kind="statement", subject_id="STMT-A"),
    "root_route to another conclusion": add("relations", {"id": "REL-ROUTE", "subject_kind": "argument",
                                                          "subject_id": "ARG-AB", "predicate": "root_route",
                                                          "object_kind": "statement", "object_id": "STMT-C"}),
    "candidate priority not an integer": mutate("candidates", "CAND-1", priority="1"),
    "claim status": mutate("claims", "CLAIM-A", status="accepted"),
    "claim attribution shape": mutate("claims", "CLAIM-A", attribution="The passage says so."),
    "claim resolves to no passage": mutate("claims", "CLAIM-A", locator="9"),
    "basis on a non-translation claim": mutate("claims", "CLAIM-A", basis="translation"),
    "unsorted edition_urns": mutate("sources", "SRC", edition_urns=["urn:cts:fix:w.b", "urn:cts:fix:w.a"]),
    "source missing field": mutate("sources", "SRC", catalog_url=""),
    "Lean declaration tail not found": mutate("statements", "STMT-D", lean_declaration="TruthCore.Fix.nowhere"),
    "shared Lean declaration": mutate("statements", "STMT-D", lean_declaration="TruthCore.Fix.fixA"),
    "settlement action shape": mutate("statements", "STMT-D", settlement_actions=[{"kind": "other"}]),
    "transcription label without field": mutate("results", "RES-BC", description="Transcription of BC."),
    "unknown transcription kind": mutate("results", "RES-BC", transcription="echo"),
    "comparator path": mutate("results", "RES-BC", comparator_config="elsewhere.json"),
    "case_split without target": mutate("results", "RES-BC", case_split={"cases": []}),
    "NanoDa disabled": comparator(lambda config: config.update(enable_nanoda=False)),
    "axioms permitted without Mathlib": comparator(
        lambda config: config.update(permitted_axioms=["propext", "Classical.choice", "Quot.sound"])),
    "theorem not in Comparator config": comparator(lambda config: config.update(theorem_names=[])),
    "bad model id": mutate("models", "MODEL-FIX", id="MODEL-fix"),
    "model evaluation of unknown statement": mutate("models", "MODEL-FIX", evaluations=[
        {"statement_id": "STMT-NOPE", "value": "satisfies", "theorem": "T.e", "arguments": []}]),
    "configuration unknown seed": mutate("configurations", "CONFIG-FIX", seed_statement_id="STMT-NOPE"),
    "configuration omits a model": mutate("configurations", "CONFIG-FIX", model_bindings=[]),
    "strength comparison without evidence": add("relations", {
        "id": "REL-CMP", "subject_kind": "statement", "subject_id": "STMT-A", "predicate": "strength_comparison",
        "object_kind": "statement", "object_id": "STMT-B", "delta_statement_id": "STMT-C",
        "background_statement_ids": [], "statement_parameter_indices": {"stronger": [], "weaker": [], "delta": []},
        "comparison_spec": "s", "note": "n", "evidence_result_ids": {}}),
    "candidate/result id collision": add("candidates", {"id": "RES-AB", "source_id": "SRC", "locator": "2",
                                                        "priority": 1, "goal": "g", "reason": "r",
                                                        "status": "candidate"}),
}


def write_check_fixture(root, change=None):
    """Write the fixture checkout, with a copy of `scripts/*.py` so the
    unmodified Python validator runs against it."""
    records = check_records()
    configs = {result["id"]: {"challenge_module": result["challenge_module"],
                              "solution_module": result["solution_module"],
                              "theorem_names": [result["theorem"]], "permitted_axioms": [],
                              "enable_nanoda": True} for result in records["results"]}
    if change is not None:
        if change.__code__.co_argcount == 2:
            change(records, configs)
        else:
            change(records)
    for kind, items in records.items():
        directory = root / "corpus" / kind
        directory.mkdir(parents=True, exist_ok=True)
        for index, record in enumerate(items):
            name = record.get("id", "x") if kind != "passages" else "p"
            (directory / f"{index:02d}-{name}.json").write_text(json.dumps(record, indent=2))
    for rid, config in configs.items():
        (root / "results" / rid).mkdir(parents=True, exist_ok=True)
        (root / "results" / rid / "comparator.json").write_text(json.dumps(config))
    for path, text in CHECK_LEAN.items():
        (root / path).parent.mkdir(parents=True, exist_ok=True)
        (root / path).write_text(text)
    (root / "scripts").mkdir(exist_ok=True)
    for script in (corpus.ROOT / "scripts").glob("*.py"):
        shutil.copy(script, root / "scripts" / script.name)


def python_check(root):
    return subprocess.run([sys.executable, str(root / "scripts" / "corpus.py"), "check"],
                          capture_output=True, text=True, check=False)


class TruthCheckParity(unittest.TestCase):
    """`truth check` against `corpus.py check`."""

    def truth_check(self, root):
        return subprocess.run([self.binary, "--root", str(root), "check"],
                              capture_output=True, text=True, check=False)

    def assert_same(self, root):
        python, rust = python_check(root), self.truth_check(root)
        rust_lines = rust.stderr.splitlines()
        self.assertTrue(rust_lines[0].startswith("notice: truth check is a partial port"), rust.stderr)
        if python.returncode == 0:
            self.assertEqual(rust.returncode, 0, rust.stderr)
            self.assertEqual(rust.stdout, python.stdout)
            self.assertEqual(rust_lines[1:], python.stderr.splitlines())
            return python.stdout.strip()
        self.assertEqual(python.returncode, 2, python.stderr)
        self.assertEqual(rust.returncode, 1, rust.stderr)
        self.assertEqual(rust.stdout, "")
        self.assertEqual(rust_lines[1:], python.stderr.splitlines())
        return python.stderr.strip()

    def test_real_corpus(self):
        python = subprocess.run([sys.executable, str(corpus.ROOT / "scripts" / "corpus.py"), "check"],
                                capture_output=True, text=True, check=False)
        rust = self.truth_check(corpus.ROOT)
        self.assertEqual(python.returncode, rust.returncode, rust.stderr)
        self.assertEqual(rust.stdout, python.stdout)
        self.assertEqual(rust.stderr.splitlines()[1:], python.stderr.splitlines())
        machine = subprocess.run([self.binary, "--json", "check"], cwd=corpus.ROOT,
                                 capture_output=True, text=True, check=False)
        report = json.loads(machine.stdout)
        self.assertEqual((report["summary"], report["complete"]), (python.stdout.strip(), False))
        self.assertTrue(report["python_only"])

    def test_fixture_passes_with_warnings(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            write_check_fixture(root)
            self.assertTrue(self.assert_same(root).startswith("corpus ok: 1 sources, 1 passages"))
            warnings = python_check(root).stderr
            for expected in ("does not count for closure rule (c)", "supports relation has no note",
                             "without strong_version_needed", "category predicate markConcrete",
                             "self_evident basis observation is not met"):
                self.assertIn(expected, warnings)
            self.assertNotIn("markAbstract", warnings)

    def test_fixture_failures(self):
        for name, change in CHECK_FAILURES.items():
            with self.subTest(name), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                write_check_fixture(root, change)
                message = self.assert_same(root)
                self.assertTrue(message.startswith("corpus error: "), (name, message))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=lambda path: Path(path).resolve())
    known, rest = parser.parse_known_args()
    TruthParity.binary = TruthThicknessParity.binary = TruthCheckParity.binary = known.binary
    TruthResearchParity.binary = TruthFrontierParity.binary = known.binary
    unittest.main(argv=[__file__, *rest])
