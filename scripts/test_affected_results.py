import json
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import affected_results as ar  # noqa: E402

SCRIPT = Path(__file__).resolve().parent / "affected_results.py"


class Fixture:
    """A tiny repository: Base <- Mid <- A.Solution, B.Solution imports Mathlib, C stands alone."""

    def __init__(self, root: Path):
        self.root = root
        self.module("TruthCore.Base", [])
        self.module("TruthCore.Mid", ["TruthCore.Base"])
        self.module("TruthCore.Unused", [])
        for name, solution_imports in (
            ("A", ["TruthCore.Mid"]),
            ("B", ["Mathlib.Analysis.SpecificLimits.Basic"]),
            ("C", []),
        ):
            self.module(f"TruthCore.Results.{name}.Challenge", ["TruthCore.Base"] if name == "A" else [])
            self.module(f"TruthCore.Results.{name}.Solution", solution_imports)
            self.result(f"RESULT-{name}", f"TruthCore.Results.{name}")

    def module(self, name: str, imports: list[str]) -> None:
        path = self.root / (name.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        header = "".join(f"import {module}\n" for module in imports)
        path.write_text(f"{header}\n/-- doc mentioning import Nothing.Here -/\ntheorem t : True := trivial\n")

    def result(self, result_id: str, prefix: str) -> None:
        config_path = f"results/{result_id}/comparator.json"
        (self.root / config_path).parent.mkdir(parents=True, exist_ok=True)
        (self.root / config_path).write_text(
            json.dumps({"challenge_module": f"{prefix}.Challenge", "solution_module": f"{prefix}.Solution"})
        )
        (self.root / "corpus/results").mkdir(parents=True, exist_ok=True)
        (self.root / f"corpus/results/{result_id}.json").write_text(
            json.dumps({"id": result_id, "comparator_config": config_path})
        )


class AffectedResultsTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.fixture = Fixture(self.root)

    def tearDown(self):
        self.tmp.cleanup()

    def select(self, *changed):
        return ar.select(self.root, changed)

    def test_transitive_import_change_selects_dependents(self):
        self.assertEqual(self.select("TruthCore/Base.lean"), ("subset", ["RESULT-A"]))
        self.assertEqual(self.select("TruthCore/Mid.lean"), ("subset", ["RESULT-A"]))

    def test_challenge_or_solution_change_selects_result(self):
        self.assertEqual(self.select("TruthCore/Results/C/Challenge.lean"), ("subset", ["RESULT-C"]))
        self.assertEqual(self.select("TruthCore/Results/B/Solution.lean"), ("subset", ["RESULT-B"]))

    def test_own_records_select_result(self):
        self.assertEqual(self.select("results/RESULT-B/comparator.json"), ("subset", ["RESULT-B"]))
        self.assertEqual(self.select("corpus/results/RESULT-C.json"), ("subset", ["RESULT-C"]))

    def test_unrelated_changes_select_nothing(self):
        self.assertEqual(
            self.select("TruthCore/Unused.lean", "corpus/statements/STMT-X.json", "docs/x.md", "TruthCore.lean"),
            ("subset", []),
        )

    def test_prefix_of_result_id_does_not_match_other_result(self):
        self.fixture.result("RESULT-A-EXTRA", "TruthCore.Results.C")
        self.assertEqual(self.select("results/RESULT-A/comparator.json"), ("subset", ["RESULT-A"]))

    def test_toolchain_and_verifier_changes_select_everything(self):
        everything = ("full", ["RESULT-A", "RESULT-B", "RESULT-C"])
        for path in (
            "lean-toolchain",
            "lakefile.toml",
            "lake-manifest.json",
            "scripts/verify-result.sh",
            "scripts/verify-all.sh",
            "scripts/verify-library.sh",
            "scripts/bootstrap-verifier.sh",
            "scripts/verifier-pins.env",
            "scripts/affected_results.py",
            "scripts/TruthCoreConstants.lean",
            "scripts/corpus.py",
            "verifier/src/main.rs",
            "verifier/Cargo.lock",
            ".github/workflows/ci.yml",
        ):
            with self.subTest(path=path):
                self.assertEqual(self.select(path, "docs/x.md"), everything)

    def test_scripts_outside_the_verifier_do_not_force_full_run(self):
        self.assertEqual(self.select("scripts/source_evidence.py", "scripts/test_corpus_frontier.py"), ("subset", []))

    def test_new_result_is_selected_through_its_records(self):
        self.fixture.module("TruthCore.Results.D.Challenge", [])
        self.fixture.module("TruthCore.Results.D.Solution", ["TruthCore.Base"])
        self.fixture.result("RESULT-D", "TruthCore.Results.D")
        mode, selected = self.select(
            "corpus/results/RESULT-D.json",
            "results/RESULT-D/comparator.json",
            "TruthCore/Results/D/Challenge.lean",
            "TruthCore/Results/D/Solution.lean",
        )
        self.assertEqual((mode, selected), ("subset", ["RESULT-D"]))

    def test_import_line_forms(self):
        self.fixture.module("TruthCore.Multi", [])
        (self.root / "TruthCore/Multi.lean").write_text(
            "public import TruthCore.Base TruthCore.Unused -- comment\nmeta import TruthCore.Mid\n"
        )
        self.assertEqual(
            ar.module_imports(self.root, "TruthCore.Multi"), ["TruthCore.Base", "TruthCore.Unused", "TruthCore.Mid"]
        )

    def test_shards_partition_and_spread_mathlib_results(self):
        ids = sorted(ar.load_results(self.root))
        shards = [ar.shard(self.root, ids, i, 2) for i in range(2)]
        self.assertEqual(sorted(shards[0] + shards[1]), ids)
        self.assertFalse(set(shards[0]) & set(shards[1]))
        self.assertIn("RESULT-B", shards[0])
        with self.assertRaises(ValueError):
            ar.shard(self.root, ids, 2, 2)

    def test_shard_count(self):
        self.assertEqual(ar.shard_count(self.root, []), 0)
        self.assertEqual(ar.shard_count(self.root, ["RESULT-A"]), 1)

    def test_external_imports(self):
        (self.root / "TruthCore.lean").write_text("import TruthCore.Results.B.Solution\nimport TruthCore.Mid\n")
        self.assertEqual(ar.external_imports(self.root), ["Mathlib.Analysis.SpecificLimits.Basic"])

    def test_cli_select_against_git_diff(self):
        git = ["git", "-C", str(self.root), "-c", "user.name=t", "-c", "user.email=t@example.com"]
        subprocess.run([*git, "init", "-q"], check=True)
        subprocess.run([*git, "add", "-A"], check=True)
        subprocess.run([*git, "commit", "-qm", "base"], check=True)
        (self.root / "TruthCore/Base.lean").write_text("theorem changed : True := trivial\n")
        subprocess.run([*git, "commit", "-qam", "change"], check=True)
        output = subprocess.run(
            [sys.executable, str(SCRIPT), "--root", str(self.root), "select", "--base", "HEAD~1"],
            check=True,
            capture_output=True,
            text=True,
        ).stdout
        self.assertEqual(output.split(), ["RESULT-A"])


REPO = SCRIPT.parent.parent
SCRIPT_REFERENCE = re.compile(r"scripts/[A-Za-z0-9_./-]*[A-Za-z0-9_]")
PY_IMPORT = re.compile(r"^\s*(?:from\s+(\w+)\s+import|import\s+(\w+))", re.MULTILINE)


class ExplorerInputsTest(unittest.TestCase):
    def test_data_only_changes_do_not_run_the_explorer(self):
        self.assertEqual(
            ar.explorer_inputs_changed(
                [
                    "corpus/statements/STMT-X.json",
                    "corpus/results/RESULT-X.json",
                    "TruthCore/Results/X/Solution.lean",
                    "TruthCore/Imports/Results.lean",
                    "results/RESULT-X/comparator.json",
                    "docs/decisions/x.md",
                    "scripts/verify-result.sh",
                    "scripts/test_corpus_frontier.py",
                ]
            ),
            [],
        )

    def test_explorer_code_changes_run_the_explorer(self):
        changed = [
            "apps/corpus-explorer/src/lib/corpus.ts",
            "apps/corpus-explorer/tests/graph-buckets.browser.test.ts",
            "bun.lock",
            "scripts/premise_dossiers.py",
            ".github/workflows/ci.yml",
        ]
        self.assertEqual(ar.explorer_inputs_changed(changed), sorted(changed))

    def test_patterns_cover_every_script_the_explorer_reads(self):
        """Every scripts/ file the build or a browser test names, and the Python those import,
        is an input. Unit tests (`src/**/*.test.ts`) run in the unconditional explorer job."""
        app = REPO / "apps" / "corpus-explorer"
        sources = [*app.glob("src/**/*.ts"), *app.glob("src/**/*.tsx")]
        referenced = {
            match
            for path in [*(p for p in sources if not p.name.endswith(".test.ts")), *app.glob("tests/*.ts")]
            for match in SCRIPT_REFERENCE.findall(path.read_text(encoding="utf-8"))
            if (REPO / match).is_file()
        }
        self.assertIn("scripts/corpus.py", referenced)
        pending = [path for path in referenced if path.endswith(".py")]
        while pending:
            text = (REPO / pending.pop()).read_text(encoding="utf-8")
            for groups in PY_IMPORT.findall(text):
                module = f"scripts/{groups[0] or groups[1]}.py"
                if (REPO / module).is_file() and module not in referenced:
                    referenced.add(module)
                    pending.append(module)
        self.assertEqual(sorted(referenced - set(ar.explorer_inputs_changed(referenced))), [])

    def test_cli_explorer_against_git_diff(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            git = ["git", "-C", tmp, "-c", "user.name=t", "-c", "user.email=t@example.com"]
            subprocess.run([*git, "init", "-q"], check=True)
            (root / "corpus").mkdir()
            (root / "corpus/a.json").write_text("{}\n")
            subprocess.run([*git, "add", "-A"], check=True)
            subprocess.run([*git, "commit", "-qm", "base"], check=True)

            def explorer():
                return subprocess.run(
                    [sys.executable, str(SCRIPT), "--root", tmp, "explorer", "--base", "HEAD~1"],
                    check=True,
                    capture_output=True,
                    text=True,
                ).stdout.strip()

            (root / "corpus/a.json").write_text('{"changed": true}\n')
            subprocess.run([*git, "commit", "-qam", "data"], check=True)
            self.assertEqual(explorer(), "false")
            (root / "package.json").write_text("{}\n")
            subprocess.run([*git, "add", "-A"], check=True)
            subprocess.run([*git, "commit", "-qm", "code"], check=True)
            self.assertEqual(explorer(), "true")


if __name__ == "__main__":
    unittest.main()
