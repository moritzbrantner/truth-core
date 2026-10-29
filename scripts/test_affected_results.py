import json
import os
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

    def test_script_changes_use_the_conservative_safety_path(self):
        self.assertEqual(self.select("scripts/source_evidence.py", "scripts/test_corpus_frontier.py"),
                         ("full", ["RESULT-A", "RESULT-B", "RESULT-C"]))

    def test_nanoda_scope_is_changed_modules_and_reverse_dependents(self):
        self.assertEqual(
            ar.nanoda_scope(self.root, ["TruthCore/Base.lean", "docs/x.md"]),
            (
                "scoped",
                [
                    "TruthCore.Base",
                    "TruthCore.Mid",
                    "TruthCore.Results.A.Challenge",
                    "TruthCore.Results.A.Solution",
                ],
            ),
        )
        self.assertEqual(
            ar.nanoda_scope(self.root, ["TruthCore/Results/C/Solution.lean"]),
            ("scoped", ["TruthCore.Results.C.Solution"]),
        )

    def test_nanoda_scope_covers_dependents_of_a_deleted_module(self):
        (self.root / "TruthCore/Mid.lean").unlink()
        self.assertEqual(
            ar.nanoda_scope(self.root, ["TruthCore/Mid.lean"]),
            ("scoped", ["TruthCore.Results.A.Solution"]),
        )

    def test_nanoda_scope_without_lean_changes_is_empty(self):
        self.assertEqual(ar.nanoda_scope(self.root, ["corpus/statements/STMT-X.json", "docs/x.md"]), ("scoped", []))

    def test_nanoda_scope_is_full_when_every_result_is_selected(self):
        for path in ("lean-toolchain", "scripts/TruthCoreConstants.lean", ".github/actions/lean-setup/action.yml"):
            with self.subTest(path=path):
                self.assertEqual(ar.nanoda_scope(self.root, [path, "TruthCore/Base.lean"]), ("full", []))

    def test_nanoda_modules_cli_reads_git_diff(self):
        def git(*args):
            subprocess.run(
                ["git", "-c", "user.name=t", "-c", "user.email=t@t", *args],
                cwd=self.root,
                check=True,
                capture_output=True,
            )

        git("init", "-q")
        git("add", "-A")
        git("commit", "-qm", "base")
        self.fixture.module("TruthCore.Mid", ["TruthCore.Base", "TruthCore.Unused"])
        git("commit", "-qam", "head")
        output = self.root / "modules.txt"
        subprocess.run(
            [
                sys.executable,
                str(SCRIPT),
                "--root",
                str(self.root),
                "nanoda-modules",
                "--base",
                "HEAD^",
                "--output",
                str(output),
            ],
            check=True,
            capture_output=True,
            env={key: value for key, value in os.environ.items() if key != "GITHUB_OUTPUT"},
        )
        self.assertEqual(output.read_text().split(), ["TruthCore.Mid", "TruthCore.Results.A.Solution"])

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


class ImpactPlanTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.fixture = Fixture(self.root)

    def plan(self, *paths, main=False):
        return ar.impact_plan(self.root, paths, main=main)

    def test_docs_only_bypasses_heavy_work_but_keeps_fast_checks(self):
        for paths in [("AGENTS.md",), ("docs/catholic-case.md", "docs/decisions/x.md"),
                      ("README.md", "CONTEXT.md", "CLAUDE.md"), ()]:
            with self.subTest(paths=paths):
                for main in (False, True):
                    plan = self.plan(*paths, main=main)
                    self.assertEqual(plan["selected"], [])
                    self.assertEqual([k for k, v in plan["checks"].items() if v], ["fast"])

    def test_leaf_and_shared_lean_keep_binding_results_and_nanoda(self):
        for path in ("TruthCore/Results/A/Solution.lean", "TruthCore/Base.lean"):
            with self.subTest(path=path):
                plan = self.plan(path)
                self.assertEqual(plan["selected"], ["RESULT-A"])
                for key in ("lean", "library_changed", "comparator_library", "report", "explorer_tests"):
                    self.assertTrue(plan["checks"][key])
                for key in ("source", "explorer", "full"):
                    self.assertFalse(plan["checks"][key])
        self.assertIn("TruthCore.Results.A.Solution", ar.nanoda_scope(self.root, ["TruthCore/Base.lean"])[1])

    def test_source_and_corpus_changes_retain_integrity_binding_and_data_tests(self):
        for path in ("corpus/passages/P.json", "corpus/claims/C.json", "corpus/sources/S.json",
                     "corpus/statements/S.json", "corpus/models/M.json", "results/RESULT-A/comparator.json"):
            with self.subTest(path=path):
                plan = self.plan(path)
                for key in ("lean", "source", "explorer_tests", "report", "comparator_library"):
                    self.assertTrue(plan["checks"][key])
                self.assertFalse(plan["checks"]["explorer"])
                self.assertFalse(plan["checks"]["library_changed"])

    def test_explorer_only_gets_live_report_and_both_browsers_without_library_recheck(self):
        for path in ("apps/corpus-explorer/src/lib/corpus.ts", "bun.lock", "package.json", "turbo.json"):
            with self.subTest(path=path):
                plan = self.plan(path)
                for key in ("explorer", "explorer_tests", "report", "comparator_library"):
                    self.assertTrue(plan["checks"][key])
                for key in ("lean", "source", "library_changed"):
                    self.assertFalse(plan["checks"][key])
                self.assertEqual(plan["selected"], [])

    def test_uncertain_tooling_generator_and_verifier_inputs_run_everything(self):
        for path in ("unknown", "docs/executable.py", "TruthCore/new.data", "scripts/new.py",
                     "scripts/source_evidence.py", "scripts/root_imports.py", "scripts/affected_results.py",
                     "scripts/test_affected_results.py", "scripts/testdata/frontier-transcription-closure.json",
                     "scripts/verifier-pins.env", ".github/workflows/ci.yml", ".github/actions/new/action.yml",
                     "verifier/README.md", "lean-toolchain", "lake-manifest.json"):
            with self.subTest(path=path):
                plan = self.plan(path)
                self.assertTrue(all(plan["checks"].values()))
                self.assertEqual(plan["selected"], ["RESULT-A", "RESULT-B", "RESULT-C"])

    def test_main_formal_changes_remain_exhaustive_without_unrelated_browsers(self):
        for path in ("TruthCore/Base.lean", "corpus/passages/P.json"):
            plan = self.plan(path, main=True)
            self.assertEqual(plan["mode"], "full")
            self.assertEqual(plan["selected"], ["RESULT-A", "RESULT-B", "RESULT-C"])
            for key in ("lean", "source", "library_changed", "report"):
                self.assertTrue(plan["checks"][key])
            self.assertFalse(plan["checks"]["explorer"])

    def test_missing_base_and_full_nightly_manual_cli(self):
        for args in (("--base", "unavailable"), ("--all",)):
            with self.subTest(args=args):
                output = self.root / "github-output"
                summary = self.root / "summary"
                output.write_text("")
                result = subprocess.run(
                    [sys.executable, str(SCRIPT), "--root", str(self.root), "select", *args],
                    env={**os.environ, "GITHUB_OUTPUT": str(output), "GITHUB_STEP_SUMMARY": str(summary)},
                    capture_output=True, text=True, check=True,
                )
                self.assertEqual(result.stdout.split(), ["RESULT-A", "RESULT-B", "RESULT-C"])
                self.assertIn("mode=full", output.read_text())
                for key in ("lean", "source", "library_changed", "explorer", "report", "comparator_library"):
                    self.assertIn(f"{key}=true", output.read_text())
                self.assertIn("not fresh formal certification", summary.read_text())

    def test_git_diff_preserves_unusual_names_and_both_sides_of_renames(self):
        git = ["git", "-C", str(self.root), "-c", "user.name=t", "-c", "user.email=t@t"]
        subprocess.run([*git, "init", "-q"], check=True)
        subprocess.run([*git, "add", "-A"], check=True)
        subprocess.run([*git, "commit", "-qm", "base"], check=True)
        path = "unexpected\nname.txt"
        (self.root / path).write_text("unknown input")
        old = "TruthCore/Base.lean"
        new = "TruthCore/Renamed.lean"
        (self.root / old).rename(self.root / new)
        subprocess.run([*git, "add", "-A"], check=True)
        subprocess.run([*git, "commit", "-qm", "rename and unknown"], check=True)
        changed = ar.git_changed_files(self.root, "HEAD^", "HEAD")
        self.assertEqual(sorted(changed), sorted([path, old, new]))
        self.assertTrue(ar.impact_plan(self.root, changed)["checks"]["full"])

    def test_docs_mixed_with_an_input_does_not_hide_the_input(self):
        for path in ("TruthCore/Base.lean", "corpus/claims/C.json", "unknown"):
            self.assertEqual(self.plan("docs/x.md", path)["checks"], self.plan(path)["checks"])


def workflow_shell(step_name):
    """Execute the actual workflow shell without adding a YAML dependency to CI tests."""
    workflow = (REPO / ".github/workflows/ci.yml").read_text()
    step = workflow.split(f"- name: {step_name}\n", 1)[1]
    lines = step.split("        run: |\n", 1)[1].splitlines()
    script = []
    for line in lines:
        if line and not line.startswith("          "):
            break
        script.append(line[10:])
    return "\n".join(script)


class ComparatorAggregateTest(unittest.TestCase):
    def gate(self, **changes):
        environment = {"PLAN": "success", "LIBRARY": "skipped", "SHARDS": "skipped", "MODE": "subset",
                       "COUNT": "0", "EXPECT_LIBRARY": "false", "EXPECT_REPORT": "false", "EXPLORER": "false"}
        environment.update(changes)
        result = subprocess.run(["bash", "-euo", "pipefail", "-c", workflow_shell("Check comparator jobs")],
                                env={**os.environ, **environment}, capture_output=True, text=True)
        return result.returncode

    def test_unaffected_and_running_branches(self):
        self.assertEqual(self.gate(), 0)
        self.assertEqual(self.gate(LIBRARY="success", EXPECT_LIBRARY="true", EXPECT_REPORT="true", EXPLORER="true"), 0)
        self.assertEqual(self.gate(LIBRARY="success", EXPECT_LIBRARY="true", EXPECT_REPORT="true",
                                   SHARDS="success", COUNT="3", MODE="full"), 0)

    def test_failures_cancellations_and_unexpected_skips_block(self):
        for change in ({"PLAN": "failure"}, {"PLAN": "skipped"}, {"COUNT": ""}, {"MODE": ""},
                       {"LIBRARY": "failure"}, {"LIBRARY": "cancelled"}, {"EXPECT_LIBRARY": ""},
                       {"EXPECT_LIBRARY": "true"}, {"COUNT": "1"}, {"SHARDS": "failure"},
                       {"SHARDS": "cancelled"}, {"MODE": "full"}, {"EXPLORER": "true"},
                       {"EXPECT_REPORT": "true"}):
            with self.subTest(change=change):
                self.assertNotEqual(self.gate(**change), 0)
        self.assertNotEqual(self.gate(EXPECT_LIBRARY="true", LIBRARY="failure", COUNT="1", SHARDS="success"), 0)
        self.assertNotEqual(self.gate(EXPECT_LIBRARY="true", LIBRARY="success", EXPECT_REPORT=""), 0)
        self.assertNotEqual(self.gate(EXPLORER=""), 0)
        self.assertNotEqual(self.gate(EXPECT_LIBRARY="true", LIBRARY="success", COUNT="1", SHARDS="success",
                                     MODE="full", EXPECT_REPORT="false"), 0)

    def test_offline_pdf_tests_always_have_poppler(self):
        workflow = (REPO / ".github/workflows/ci.yml").read_text()
        corpus = workflow.split("  corpus-and-lean:\n", 1)[1].split("\n  corpus-explorer:", 1)[0]
        install = corpus.split("- name: Install PDF source extraction\n", 1)[1].split("      - name:", 1)[0]
        tests = corpus.split("- name: Test corpus tooling and media-span and web-snapshot evidence offline\n", 1)[1].split("      - name:", 1)[0]
        self.assertIn("apt-get install -y poppler-utils", install)
        self.assertNotIn("if:", install)
        self.assertIn("python3 -m unittest discover", tests)
        self.assertNotIn("if:", tests)
        self.assertLess(corpus.index(install), corpus.index(tests))

    def test_workflow_gates_keep_stable_checks_and_live_browser_dependency(self):
        workflow = (REPO / ".github/workflows/ci.yml").read_text()
        for job in ("corpus-explorer-browser-root", "corpus-explorer-browser-pages"):
            block = workflow.split(f"  {job}:\n", 1)[1].split("\n  #", 1)[0]
            self.assertIn("needs: [comparator-plan, comparator-library]", block)
            self.assertIn("if: needs.comparator-plan.outputs.explorer == 'true'", block)
        self.assertIn("if: needs.comparator-plan.outputs.comparator_library == 'true'", workflow)
        self.assertIn("if: needs.comparator-plan.outputs.explorer_tests == 'true'", workflow)
        for step in ("Bind argument records to result theorem types", "Verify immutable primary-source witnesses"):
            self.assertIn("if: needs.comparator-plan.outputs.", workflow.split(f"- name: {step}\n")[1].split("run:")[0])


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
            "scripts/bundle_audit.py",
            "scripts/expression_contracts.py",
            "scripts/contracts/classical-attributes.json",
            "docs/notes/classical-attributes-migration.json",
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
