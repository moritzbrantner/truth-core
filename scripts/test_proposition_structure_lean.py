"""Focused integration regressions against elaborated Lean, including checked separators."""
import json
import os
from pathlib import Path
import subprocess
import shutil
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
NS = "TruthCore.InspectorFixture."


def walk(node):
    yield node
    for child in node["children"]:
        yield from walk(child["node"])


@unittest.skipUnless(shutil.which("lake") or (Path.home() / ".elan/bin/lake").exists(), "Lean integration requires lake")
class ElaboratedStructureTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory()
        directory = Path(cls.temp.name)
        run = ["python3", "scripts/worker_env.py", "--", "lake", "env"]
        subprocess.run(run + ["lean", "-o", str(directory / "InspectorFixture.olean"),
                              "scripts/fixtures/PropositionStructure.lean"], cwd=ROOT, check=True,
                       capture_output=True, text=True)
        names = ["forward", "reverse", "shared", "separate", "alternating", "uniform",
                 "grouped", "groupedOther", "equivalence", "model"]
        request = directory / "request.json"
        request.write_text(json.dumps({"modules": ["InspectorFixture"],
            "declarations": [NS + n for n in names], "unfold": [NS + n for n in names]}))
        env = dict(os.environ)
        env["LEAN_PATH"] = str(directory) + os.pathsep + env.get("LEAN_PATH", "")
        output = subprocess.run(run + ["lean", "--run", "scripts/PropositionStructure.lean", str(request)],
                                cwd=ROOT, env=env, check=True, capture_output=True, text=True)
        limited = json.loads(request.read_text())
        limited["max_depth"] = 2
        request.write_text(json.dumps(limited))
        partial = subprocess.run(run + ["lean", "--run", "scripts/PropositionStructure.lean", str(request)],
                                 cwd=ROOT, env=env, check=True, capture_output=True, text=True)
        cls.partial = json.loads(partial.stdout)
        cls.reports = {r["declaration"].removeprefix(NS): r for r in json.loads(output.stdout)}

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def nodes(self, name):
        return list(walk(self.reports[name]["expansion"]))

    def test_ordered_application_binding(self):
        def arguments(name):
            app = next(n for n in self.nodes(name) if n["kind"] == "application")
            return [c["node"]["binding"].split("/expansion", 1)[1] for c in app["children"][1:]]
        self.assertEqual(arguments("forward"), list(reversed(arguments("reverse"))))

    def test_shared_and_separate_existentials(self):
        self.assertEqual(sum(n["kind"] == "exists" for n in self.nodes("shared")), 1)
        self.assertEqual(sum(n["kind"] == "exists" for n in self.nodes("separate")), 2)
        # All references resolve within the exact elaborated expression scope.
        for name in ["shared", "separate", "alternating", "uniform"]:
            nodes = self.nodes(name)
            ids = {n["id"] for n in nodes}
            self.assertTrue(all(n["binding"] in ids for n in nodes if "binding" in n))

    def test_quantifier_order_and_grouping(self):
        kinds = lambda name: [n["kind"] for n in self.nodes(name)
                               if n["kind"] in ["forall", "exists", "and", "or"] and "/domain" not in n["id"] and "/function" not in n["id"]]
        self.assertEqual(kinds("alternating"), ["forall", "exists"])
        self.assertEqual(kinds("uniform"), ["exists", "forall"])
        self.assertEqual(kinds("grouped"), ["or", "and"])
        self.assertEqual(kinds("groupedOther"), ["and", "or"])
        self.assertTrue(any(n["kind"] == "iff" for n in self.nodes("equivalence")))
        self.assertFalse(any("selected_branch" in n for n in self.nodes("grouped")))

    def test_partial_depth_limit_is_visible_and_typed(self):
        nodes = [n for r in self.partial for n in walk(r["expansion"])]
        unsupported = [n for n in nodes if n["kind"] == "unsupported"]
        self.assertTrue(unsupported)
        self.assertTrue(all(n["coverage"].startswith("partial:") and n["type"] for n in unsupported))
        self.assertTrue(all("atom" not in n for n in unsupported))

    def test_types_and_reachable_laws(self):
        self.assertTrue(all(n["type"] for n in self.nodes("model")))
        refs = self.reports["model"]["references"]
        lawful = next(r for r in refs if r["declaration"] == NS + "LawfulRelation")
        law = next(f for f in lawful["fields"] if f["declaration"].endswith(".reflexive"))
        self.assertTrue(law["is_law"])


if __name__ == "__main__":
    unittest.main()
