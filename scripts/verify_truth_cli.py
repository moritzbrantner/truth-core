#!/usr/bin/env python3
"""Compare the Rust CLI with the existing Python corpus readers: the
structural view (`status`, `inspect`), `thickness [--queue]` and `check`."""
import argparse
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
    TruthParity.binary = TruthThicknessParity.binary = TruthCheckParity.binary = parser.parse_args().binary
    unittest.main(argv=[__file__])
