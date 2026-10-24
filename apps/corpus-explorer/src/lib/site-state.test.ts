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

  test("transcriptions are the single-application results", () => {
    const transcriptions = corpus.results.filter((result) => resultKind(report, result.id).kind === "transcription");
    expect(transcriptions.length).toBe(report.transcription_flags.filter((flag) => flag.single_application_of).length);
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
