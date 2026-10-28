import { expect, test } from "bun:test";

import { selectedConfiguration } from "./configuration-selection";
import { parseVerifiedConfigurations, type CertifiedSelection, type VerifiedConfigurationBundle } from "./verified-configurations";

// Transport fixtures are not corpus registrations or evidence of verification.
function selection(status: CertifiedSelection["status"]): CertifiedSelection {
  return { id: "selection", statement_ids: [], status, incompatible_cores: status === "verified incompatible" ? [{
    statement_ids: ["P"], result_id: "R", theorem: "Fixture.contradiction", result_ids: ["R"], theorems: ["Fixture.contradiction"],
    minimality: "fixture", removal_evidence: [{ removed_statement_id: "P", model_ids: ["M"] }],
  }] : [], model_ids: status === "model witnessed" ? ["M"] : [],
  model_witnesses: status === "model witnessed" ? [{ model_id: "M", lean_declaration: "Fixture.model", evaluations: [] }] : [],
  unresolved_reason: status === "unresolved" ? "No available certificate" : null,
  core_composition: { combinations_checked: 1, limit: 128, truncated: false } };
}
function fixture(): VerifiedConfigurationBundle {
  return { schema_version: 1, producer: { mode: "live-verified", source_head: "a".repeat(40), input_digest: "b".repeat(64), trust: "Trusted test producer shape; not a proof." }, cases: [{
    id: "CONFIG-FIXTURE", seed_statement_id: "P", verified: true,
    semantics: { id: "fixture", logic: "fixture", frame: "fixture", domain: "fixture", identity: "fixture", vocabulary: "fixture" },
    configurations: [], scope: "Transport fixture only", inapplicable_models: [], verified_implications: [],
    verification: { result_ids: ["R"], original_bound_result_ids: ["R"], models: { models: 1, certificates: 1, axioms: [] }, compositions: { cores: 1 } },
    family_verification: { cores: 1 },
    assumption_space: { statement_ids: ["P", "Q"], max_dimensions: 10, root: "root", nodes: [
      { id: "root", kind: "decision", statement_id: "P", exclude: "model", include: "core" },
      { id: "model", kind: "terminal", required_statement_ids: [], optional_statement_ids: ["Q"], syntactic_selections_covered: 2, report: selection("model witnessed") },
      { id: "core", kind: "terminal", required_statement_ids: ["P"], optional_statement_ids: ["Q"], syntactic_selections_covered: 2, report: selection("verified incompatible") },
    ], limits: { classifier_calls: 3, decision_nodes: 1, terminal_families: 2, syntactic_selections: 4, covered_selections: 4, note: "Syntactic selections only" } },
  }] };
}

test("browser traverses certified families and rejects unsupported or circular paths", () => {
  const space = fixture().cases[0]!.assumption_space;
  for (const ids of [[], ["Q"]]) { expect(selectedConfiguration(space, ids).terminal?.report.status).toBe("model witnessed"); }
  for (const ids of [["P"], ["P", "Q"]]) { expect(selectedConfiguration(space, ids).terminal?.report.status).toBe("verified incompatible"); }
  expect(selectedConfiguration(space, ["UNKNOWN"]).error).toContain("unsupported");
  expect(selectedConfiguration(space, ["P", "P"]).error).toContain("repeated");
  const cyclic = { ...space, nodes: space.nodes.map((node) => node.kind === "decision" ? { ...node, include: "root" } : node) };
  expect(selectedConfiguration(cyclic, ["P"]).error).toContain("circular");
});

test("certified transport requires producer, proof provenance, bounded dimensions and valid edges", () => {
  expect(parseVerifiedConfigurations(fixture()).cases[0]?.verified).toBe(true);
  const original = fixture();
  expect(() => parseVerifiedConfigurations({ ...original, schema_version: 2 })).toThrow();
  expect(() => parseVerifiedConfigurations({ ...original, producer: { ...original.producer, mode: "registered" } })).toThrow();
  const configuration = original.cases[0]!;
  expect(() => parseVerifiedConfigurations({ ...original, cases: [{ ...configuration, verified: false }] })).toThrow();
  expect(() => parseVerifiedConfigurations({ ...original, cases: [{ ...configuration, verification: undefined }] })).toThrow();
  const dimensions = ["P", "Q", ...Array.from({ length: 8 }, (_, i) => `DIMENSION_${i}`)];
  const expanded = { ...configuration.assumption_space, statement_ids: dimensions,
    nodes: configuration.assumption_space.nodes.map((entry) => entry.kind === "terminal"
      ? { ...entry, optional_statement_ids: dimensions.slice(1), syntactic_selections_covered: 512 } : entry),
    limits: { ...configuration.assumption_space.limits, syntactic_selections: 1024, covered_selections: 1024 } };
  expect(parseVerifiedConfigurations({ ...original, cases: [{ ...configuration, assumption_space: expanded }] }).cases[0]?.assumption_space.statement_ids).toEqual(dimensions);
  expect(() => parseVerifiedConfigurations({ ...original, cases: [{ ...configuration, assumption_space: { ...configuration.assumption_space, statement_ids: [...dimensions, "OVER_LIMIT"] } }] })).toThrow();
  expect(() => parseVerifiedConfigurations({ ...original, cases: [{ ...configuration, assumption_space: { ...configuration.assumption_space, max_dimensions: 11 } }] })).toThrow();
  expect(() => parseVerifiedConfigurations({ ...original, cases: [{ ...configuration, assumption_space: { ...configuration.assumption_space, root: "MISSING" } }] })).toThrow();
});
