import { describe, expect, test } from "bun:test";

import { getCorpus } from "./corpus";
import { indexLeanSource, leanIndex, theoremInModule } from "./lean-source";
import { getFrontierReport, resultKind, statementState } from "./site-state";

describe("state of the case (#200)", () => {
  const corpus = getCorpus();
  const report = getFrontierReport();

  test("every statement and frontier item has a state from corpus.py", () => {
    for (const item of report.items) {
      expect(statementState(report, item.statement_id).kind).toBe("open");
    }
    for (const id of Object.keys(report.closed_statements)) {
      expect(statementState(report, id).kind).toBe("closed");
    }
    expect(statementState(report, "STMT-EXCLUDED-MIDDLE")).toEqual({ kind: "closed", reason: "self_evident", established: true });
    expect(statementState(report, "STMT-CATHOLICISM-TRUE")).toMatchObject({ kind: "closed", established: false });
  });

  test("transcriptions are the results corpus.py lists as transcriptions", () => {
    const transcriptions = corpus.results.filter((result) => resultKind(report, result.id).kind === "transcription");
    expect(transcriptions.length).toBe(Object.keys(report.transcription_results).length);
    // Declared in the record (#391), or found by the single-application and assembly heuristics.
    for (const result of corpus.results) {
      const declared = result.transcription;
      if (declared) expect(resultKind(report, result.id).transcription).toEqual({ kind: declared, declared: true });
    }
    for (const flag of report.transcription_flags) {
      if (flag.single_application_of || flag.assembly_of) expect(resultKind(report, flag.result_id).kind).toBe("transcription");
    }
  });

  test("a refutation counts only from closed premises", () => {
    for (const refutation of report.refutations) {
      expect(report.refuted_statements.includes(refutation.statement_id) || !refutation.counted).toBe(true);
      if (refutation.counted) expect(refutation.open_premise_statement_ids).toEqual([]);
    }
  });

  test("resolves every statement's Lean declaration and every advertised theorem", () => {
    const index = leanIndex();
    for (const statement of corpus.statements) {
      if (statement.lean_declaration) expect(index.has(statement.lean_declaration)).toBe(true);
    }
    for (const result of corpus.results) {
      expect(theoremInModule(result.challenge_module, result.theorem)?.snippet).toContain("sorry");
    }
  });

  test("indexes namespaced declarations with their doc comment", () => {
    const [location] = indexLeanSource(
      "X.lean",
      ["namespace A.B", "", "/-- Doc. -/", "def P (x : Nat) : Prop :=", "  x = x", "", "end A.B"].join("\n"),
    );
    expect(location).toEqual({ name: "A.B.P", file: "X.lean", line: 4, snippet: "/-- Doc. -/\ndef P (x : Nat) : Prop :=\n  x = x" });
  });
});
