import { expect, test } from "bun:test";
import { certificateOutcome, comparisonOutcomes, senseCellOutcome } from "./research-progress";
import type { RegisteredConfigurationCase } from "./configuration-cases";
import type { VerifiedConfigurationCase } from "./verified-configurations";

const registered: RegisteredConfigurationCase = {
  id: "case", seed_statement_id: "target", verified: false, scope: "same witness only",
  semantics: { id: "profile", logic: "classical", frame: "one", domain: "finite", identity: "literal", vocabulary: "V" },
  inapplicable_models: [], configurations: [{ id: "open", statement_ids: ["P"], status: "verification required", incompatible_cores: [{ statement_ids: ["P"], result_id: "R", theorem: "T", minimality: "unknown" }], model_ids: ["M"] }],
};
test("registered cores and models confer no verified outcome", () => {
  expect(comparisonOutcomes(registered)).toEqual([{ id: "open", status: "verification required", premises: ["P"] }]);
});
test("preserves certified exclusion, model compatibility and exact unresolved scope", () => {
  const certified: VerifiedConfigurationCase = { ...registered, verified: true,
    verification: { result_ids: [], original_bound_result_ids: [], models: { models: 0, certificates: 0, axioms: [] }, compositions: { cores: 0 } }, family_verification: { cores: 0 }, verified_implications: [],
    assumption_space: { statement_ids: [], max_dimensions: 11, root: "x", nodes: [], limits: { classifier_calls: 0, decision_nodes: 0, terminal_families: 0, syntactic_selections: 0, covered_selections: 0, note: "bounded" } },
    configurations: (["verified incompatible", "model witnessed", "unresolved"] as const).map((status, index) => ({ id: String(index), statement_ids: ["P"], status, incompatible_cores: [], model_ids: [], model_witnesses: [], unresolved_reason: "missing joint witness", core_composition: { combinations_checked: 0, limit: 1, truncated: false } })),
  };
  expect(comparisonOutcomes(certified).map((cell) => cell.status)).toEqual(["verified incompatible", "model witnessed", "unresolved"]);
  expect(comparisonOutcomes(certified).every((cell) => cell.premises.includes("P"))).toBe(true);
});
test("missing sense evidence stays untested despite nearby results or successful attempts", () => {
  expect(senseCellOutcome()).toBe("Untested: no explicit sense × rival certificate mapping.");
  expect(senseCellOutcome()).not.toContain("established");
});

test("explicit certificate outcomes retain conditional scope and transcription cannot certify a cell", () => {
  expect(certificateOutcome("excluded", false)).toBe("checked exclusion under recorded conditions");
  expect(certificateOutcome("model-witnessed", false)).toBe("model-witnessed compatibility under recorded conditions");
  expect(certificateOutcome("unresolved", false)).toBe("unresolved");
  expect(certificateOutcome("untested", false)).toBe("untested");
  expect(certificateOutcome(undefined, false)).toBe(senseCellOutcome());
  expect(certificateOutcome("excluded", true)).toBe("unresolved: owning result is a transcription");
});
