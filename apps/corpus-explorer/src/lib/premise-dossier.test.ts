import { describe, expect, test } from "bun:test";

import { legacyUuid } from "./corpus-ids";
import { getAttempts, getDossiers, parseDossiers, type PremiseDossier } from "./premise-dossier";

function example(): PremiseDossier {
  return {
    statement: { id: "P", paraphrase: "An open premise" }, root: "R", closure: null, established: false, frontier: { depth: "bare", path_to_root: ["P", "ARG", "R"] },
    claim_ids: [], supporting_claim_ids: [], definition_ids: [], disambiguation_ids: [], argument_ids: ["ARG"], result_ids: [],
    transcription_result_ids: [], instantiation_result_ids: [], alternative_relation_ids: [], objection_relation_ids: [], countermodel_attempt_ids: [],
    attempts: [{ id: "ATTEMPT-P", statement_ids: ["P"], date: "2026-10-26", kind: "source-search", outcome: "blocked", summary: "Missing witness", evidence: ["PR-413"], blocker: "Witness required" }],
    model_evaluations: [],
    route_contributions: [{ argument_id: "ARG", cost: 1, open_leaf: true, direct_premise: true }],
  };
}

describe("dossier transport", () => {
  test("successful attempts never manufacture establishment or closure", () => {
    const value = example();
    value.attempts = [{ ...value.attempts[0], outcome: "succeeded" }];
    const parsed = parseDossiers({ P: value }).P;
    expect(parsed.established).toBe(false);
    expect(parsed.closure).toBeNull();
  });
  test("accepts an open premise with a blocked attempt without altering status", () => {
    const value = example();
    expect(parseDossiers({ P: value })).toEqual({ P: value });
    expect(value.closure).toBeNull();
  });
  test("rejects mismatched IDs, malformed references and invalid route/status fields", () => {
    for (const value of [null, [], { Q: example() }, { P: { ...example(), attempts: [{ ...example().attempts[0], outcome: "proved" }] } },
      { P: { ...example(), closure: "true" } }, { P: { ...example(), claim_ids: [1] } },
      { P: { ...example(), route_contributions: [{ argument_id: "ARG", cost: -1, open_leaf: true, direct_premise: true }] } }]) {
      expect(() => parseDossiers(value)).toThrow();
    }
  });
  test("real corpus projection includes durable attempts and exact route membership", () => {
    const dossiers = getDossiers();
    const attempts = getAttempts();
    const p = dossiers[legacyUuid("statement", "STMT-ACT-SIMPLY-PRIOR-TO-POTENCY")];
    expect(p?.attempts.some((entry) => entry.id === legacyUuid("attempt", "ATTEMPT-ACT-POTENCY-INDEPENDENCE"))).toBe(true);
    expect(p?.model_evaluations.some((model) => model.model_id === legacyUuid("model", "MODEL-ACT-POTENCY-M3") && model.value === "violates")).toBe(true);
    expect(p?.established).toBe(false);
    expect(p?.route_contributions.some((entry) => entry.open_leaf)).toBe(true);
    expect(dossiers[legacyUuid("statement", "STMT-NOTHING-ELSE-REACHES-THE-PRIMARY")]?.attempts.find((entry) => entry.id === legacyUuid("attempt", "ATTEMPT-STRICT-PRIMACY-READING"))?.outcome).toBe("failed");
    expect(Object.keys(attempts).sort()).toEqual([...new Set(Object.values(dossiers).flatMap((entry) => entry.attempts.map((attempt) => attempt.id)))].sort());
    expect(attempts[legacyUuid("attempt", "ATTEMPT-ACT-POTENCY-INDEPENDENCE")]?.statement_ids).toContain(legacyUuid("statement", "STMT-ACT-SIMPLY-PRIOR-TO-POTENCY"));
  }, 90_000);
});
