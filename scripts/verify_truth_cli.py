#!/usr/bin/env python3
"""Compare the Rust CLI with the existing Python corpus readers: the
structural view (`status`, `inspect`) and `thickness [--queue]`."""
import argparse
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


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=lambda path: Path(path).resolve())
    TruthParity.binary = TruthThicknessParity.binary = parser.parse_args().binary
    unittest.main(argv=[__file__])
