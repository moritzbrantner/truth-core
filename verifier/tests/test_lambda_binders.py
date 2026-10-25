"""Real CLI regressions; requires Lean and the pinned lean4export toolchain.

Run after cargo build:
  python3 verifier/tests/test_lambda_binders.py verifier/target/debug/truth-core-comparator
Optional LEAN4EXPORT overrides ~/.cache/truth-core-verifier/.../lean4export.
Only build/export transport is replayed; the production parser, comparison,
dependency walk and axiom policy run unchanged. These tests do not test sandboxing.
"""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

BINARY = Path(sys.argv.pop(1)).resolve()
EXPORTER = Path(os.environ.get("LEAN4EXPORT", str(Path.home() / ".cache/truth-core-verifier/lean4export/.lake/build/bin/lean4export")))
PRIMITIVES = ["Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce"]


def run(*args, **kwargs):
    return subprocess.run(args, text=True, capture_output=True, check=True, timeout=180, **kwargs)


class LambdaBinders(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="comparator-lambda-")
        cls.root = Path(cls.temporary.name)
        # Resolve inside the repository, then pin that compiler even though the
        # disposable fixture project has no elan toolchain file.
        repository = Path(__file__).resolve().parents[2]
        prefix = run("lean", "--print-prefix", cwd=repository).stdout.strip()
        cls.env = {**os.environ, "LEAN_PATH": str(cls.root), "PATH": str(Path(prefix) / "bin") + os.pathsep + os.environ["PATH"]}
        source = (Path(__file__).parent / "fixtures/LambdaData.lean").read_text()
        cls.exports = {}
        for module, text in [("Challenge", source), ("ForbiddenAxiom", source.replace("  ⟨rfl, rfl⟩", "  Classical.choice ⟨⟨rfl, rfl⟩⟩")), ("DifferentBody", source.replace("def frozen (n : Nat) : Nat := n + 0", "def frozen (n : Nat) : Nat := n + 1"))]:
            (cls.root / f"{module}.lean").write_text(text)
            result = run("lean", "-o", f"{module}.olean", f"{module}.lean", cwd=cls.root, env=cls.env)
            assert "does not depend on any axioms" in result.stdout
            exported = run(str(EXPORTER), module, "--", "Nat", "String", "String.mk", "Char", "goal", *PRIMITIVES, cwd=cls.root, env=cls.env)
            cls.exports[module] = [json.loads(line) for line in exported.stdout.splitlines()]
        transport = cls.root / "transport"
        transport.write_text('''#!/bin/sh
while [ "$1" != "--" ]; do shift; done
shift
case "$1" in
  lake) exit 0 ;;
  replay) shift; cat "$1.ndjson" ;;
  *) exec "$@" ;;
esac
''')
        transport.chmod(0o755)
        cls.env.update(COMPARATOR_LANDRUN=str(transport), COMPARATOR_LEAN4EXPORT="replay")
        (cls.root / "config.json").write_text(json.dumps(dict(challenge_module="Challenge", solution_module="Solution", theorem_names=["goal"], permitted_axioms=[])))

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def compare(self, solution, expected=None, challenge=None):
        for module, items in [("Challenge", challenge or self.exports["Challenge"]), ("Solution", solution)]:
            (self.root / f"{module}.ndjson").write_text("\n".join(map(json.dumps, items)) + "\n")
        result = subprocess.run([str(BINARY), "config.json"], cwd=self.root, env=self.env, text=True, capture_output=True, timeout=180)
        if expected is None:
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("Your solution is okay!", result.stdout)
        else:
            self.assertEqual(result.returncode, 1, result.stderr)
            self.assertIn(expected, result.stderr)

    def dependency(self, items, name, field="value"):
        names = {0: "_"}
        for item in items:
            if "in" in item:
                data = item.get("str", item.get("num"))
                prefix = names[data["pre"]]
                names[item["in"]] = str(data.get("str", data.get("i"))) if prefix == "_" else prefix + "." + str(data.get("str", data.get("i")))
            if "def" in item and names[item["def"]["name"]] == name:
                index = item["def"][field]
                return next(x for x in items if x.get("ie") == index)
        self.fail(f"missing dependency {name}")

    def test_valid_lambda_annotations(self):
        for annotation in ["default", "implicit", "strictImplicit", "instImplicit"]:
            with self.subTest(annotation=annotation):
                items = copy.deepcopy(self.exports["Challenge"])
                self.dependency(items, "frozen")["lam"]["binderInfo"] = annotation
                self.compare(items)

    def test_raw_proof_axiom_is_still_rejected(self):
        self.compare(self.exports["ForbiddenAxiom"], "illegal axiom detected: Classical.choice")

    def test_same_type_different_data_body(self):
        # Both source programs above kernel-check; goal's exact type is unchanged.
        self.compare(self.exports["DifferentBody"], "constant does not match between challenge and solution: frozen (value)")

    def test_lambda_domain_and_body_structure(self):
        for field in ["type", "body"]:
            with self.subTest(field=field):
                items = copy.deepcopy(self.exports["Challenge"])
                lam = self.dependency(items, "frozen")["lam"]
                lam[field] = next(x["ie"] for x in items if x.get("sort") == 0)
                self.compare(items, "constant does not match between challenge and solution: frozen (value)")

    def test_dependent_binder_type_and_de_bruijn_structure(self):
        for field in ["type", "body"]:
            with self.subTest(field=field):
                items = copy.deepcopy(self.exports["Challenge"])
                outer = self.dependency(items, "dependent")["lam"]
                inner = next(x for x in items if x.get("ie") == outer["body"])["lam"]
                # Both x's domain and returned x use de Bruijn 0; 1 changes the dependency.
                new_index = max(x.get("ie", 0) for x in items) + 1
                items.append({"ie": new_index, "bvar": 1})
                inner[field] = new_index
                self.compare(items, "constant does not match between challenge and solution: dependent (value)")

    def test_forall_annotation_stays_exact(self):
        items = copy.deepcopy(self.exports["Challenge"])
        self.dependency(items, "frozen", "type")["forallE"]["binderInfo"] = "implicit"
        self.compare(items, "constant does not match between challenge and solution: frozen (type)")

    def test_invalid_and_missing_lambda_metadata(self):
        for annotation in [None, 17, "unknown", "MISSING"]:
            with self.subTest(annotation=annotation):
                items = copy.deepcopy(self.exports["Challenge"])
                lam = self.dependency(items, "frozen")["lam"]
                if annotation == "MISSING":
                    del lam["binderInfo"]
                    expected = "binder lacks binderInfo"
                else:
                    lam["binderInfo"] = annotation
                    expected = "invalid lambda binderInfo"
                # Reject even if both exports have the same malformed annotation.
                self.compare(items, expected, challenge=items)


if __name__ == "__main__":
    unittest.main()
