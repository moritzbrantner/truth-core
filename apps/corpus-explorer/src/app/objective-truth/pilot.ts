import { execFileSync } from "node:child_process";
import path from "node:path";

/** A reading guide over canonical IDs, never another proposition or status store. */
export const PILOT_GROUPS = [
  {
    title: "The two logical propositions",
    scope: "These exact Lean propositions have premise-free proofs. They do not by themselves say that truth is independent of minds or endorsement.",
    statementIds: ["STMT-SOME-LEAN-PROPOSITION-HOLDS", "STMT-NOT-EVERY-LEAN-PROPOSITION-FAILS"],
  },
  {
    title: "Interpretation bridges still to defend",
    scope: "A logical proof does not supply an interpretation of ordinary truth or of expressed negation. The verified conditional tests retain these open premises.",
    statementIds: ["STMT-PILOT-LOGICAL-SENTENCE-STABLE", "STMT-PILOT-NEGATION-RESPECTED"],
  },
  {
    title: "Distinct readings of relativity",
    scope: "Global variation, local variation, an unindexed all-opinions-true thesis, and an epistemic limitation are different readings. Their identities remain separate.",
    statementIds: ["STMT-PILOT-GLOBAL-PROFILE-VARIATION", "STMT-PILOT-LOCAL-PROFILE-VARIATION", "STMT-ALL-OPINIONS-TRUE-UNINDEXED", "STMT-PILOT-OPPOSED-OPINIONS", "STMT-PILOT-CONFLICTING-OPINIONS", "STMT-ARIST-DEMOCRITUS-NO-TRUTH-OR-UNKNOWN"],
  },
  {
    title: "What the tests establish",
    scope: "These are conditional consequences or models of the stated encoding. They do not establish a full worldview, source fidelity, or an unconditional self-refutation of relativism.",
    statementIds: ["STMT-PILOT-NOT-GLOBAL-PROFILE-VARIATION", "STMT-PILOT-NOT-ALL-OPINIONS-TRUE", "STMT-PILOT-LOCAL-VARIATION-COMPATIBLE", "STMT-PILOT-GLOBAL-VARIATION-MODEL", "STMT-PILOT-EPISTEMIC-DIFFERENCES-MODEL"],
  },
] satisfies Array<{ title: string; scope: string; statementIds: string[] }>;

export function pilotGraphHref(statementId: string) {
  const params = new URLSearchParams({
    view: "focus", node: statementId, sel: statementId,
    scope: "goal", target: statementId, cluster: "namespace",
  });
  return `/graph?${params}`;
}

export type PilotScenario = { id: string; established: string[]; verifiedResults: number };
let cachedScenarios: PilotScenario[] | undefined;

/** Reuse Python's authoritative computation with explicit verifier-record subsets.
 * Removing a record simulates unavailable grounding; it does not undo a theorem. */
export function getPilotScenarios(): PilotScenario[] {
  if (!cachedScenarios) {
    const raw: unknown = JSON.parse(execFileSync("python3", ["-c", `
import json, sys
from pathlib import Path
sys.path.insert(0, 'scripts')
from corpus import load_dir, frontier_report
fixture = json.loads(Path('scripts/testdata/objective-truth-pilot.json').read_text())
def selected(kind, ids):
    return [x for _, x in load_dir(kind) if x['id'] in ids]
statements = selected('statements', fixture['statement_ids'])
arguments = selected('arguments', fixture['argument_ids'])
out = []
for case in fixture['cases']:
    results = selected('results', case['result_ids'])
    report = frontier_report(statements, arguments, results, [], root=fixture['statement_ids'][0])
    out.append(dict(id=case['id'], established=report['established_statements'], verifiedResults=len(results)))
print(json.dumps(out))
`], { cwd: path.resolve(process.cwd(), "../.."), encoding: "utf8" }));
    if (!Array.isArray(raw)) {
      throw new Error("Invalid pilot scenario report");
    }
    cachedScenarios = raw.map((item: unknown) => {
      if (typeof item !== "object" || item === null || !("id" in item) || typeof item.id !== "string" ||
          !("established" in item) || !Array.isArray(item.established) ||
          !item.established.every((id: unknown) => typeof id === "string") ||
          !("verifiedResults" in item) || typeof item.verifiedResults !== "number") {
        throw new Error("Invalid pilot scenario record");
      }
      return { id: item.id, established: item.established, verifiedResults: item.verifiedResults };
    });
  }
  return cachedScenarios;
}
