import { expect, test } from "bun:test";

import { getCorpus } from "@/lib/corpus";
import { getFrontierReport } from "@/lib/site-state";
import type { CertifiedSelection, VerifiedConfigurationCase } from "@/lib/verified-configurations";

import { buildAtlasModel, certifiedCores, certifiedMosaic, frontierTiles, routeImpact } from "./atlas-model";

function certified(status: CertifiedSelection["status"]): CertifiedSelection {
  return {
    id: status,
    statement_ids: [],
    status,
    incompatible_cores: status === "verified incompatible" ? [{
      statement_ids: ["P", "Q"], result_id: "R", theorem: "Fixture.r",
      result_ids: ["R"], theorems: ["Fixture.r"], minimality: "fixture only",
      removal_evidence: [{ removed_statement_id: "P", model_ids: ["M"] }],
    }] : [],
    model_ids: status === "model witnessed" ? ["M"] : [],
    model_witnesses: [],
    unresolved_reason: status === "unresolved" ? "fixture missing evidence" : null,
    core_composition: { combinations_checked: 1, limit: 10, truncated: false },
  };
}

function fixture(): VerifiedConfigurationCase {
  const impossible = certified("verified incompatible");
  const witnessed = certified("model witnessed");
  return {
    id: "CONFIG-FIXTURE", seed_statement_id: "P", scope: "Test-only case", verified: true,
    semantics: { id: "fixture", logic: "fixture", frame: "fixture", domain: "fixture", identity: "fixture", vocabulary: "fixture" },
    configurations: [impossible, impossible], inapplicable_models: [], verified_implications: [],
    verification: { result_ids: ["R"], original_bound_result_ids: ["R"], models: { models: 1, certificates: 1, axioms: [] }, compositions: { cores: 1 } },
    family_verification: { cores: 1 },
    assumption_space: {
      statement_ids: ["P", "Q"], max_dimensions: 10, root: "root",
      nodes: [
        { id: "root", kind: "decision", statement_id: "P", exclude: "witness", include: "impossible" },
        { id: "witness", kind: "terminal", required_statement_ids: [], optional_statement_ids: ["Q"], report: witnessed, syntactic_selections_covered: 2 },
        { id: "impossible", kind: "terminal", required_statement_ids: ["P"], optional_statement_ids: ["Q"], report: impossible, syntactic_selections_covered: 2 },
      ],
      limits: { classifier_calls: 2, decision_nodes: 1, terminal_families: 2, syntactic_selections: 4, covered_selections: 4, note: "Test fixture" },
    },
  };
}

test("atlas partitions real open premises exactly once and keeps root reachability separate from source depth", () => {
  const report = getFrontierReport();
  const model = buildAtlasModel(getCorpus(), report);
  const tiles = frontierTiles(model.premises);
  expect(model.premises.length).toBe(report.open_premise_count);
  expect(tiles.reduce((total, tile) => total + tile.count, 0)).toBe(report.open_premise_count);
  expect(tiles.filter((tile) => tile.depth === "bare").reduce((total, tile) => total + tile.count, 0)).toBe(report.depth_counts.bare);
  expect(tiles.filter((tile) => tile.depth === "sourced").reduce((total, tile) => total + tile.count, 0)).toBe(report.depth_counts.sourced);
  expect(new Set(tiles.flatMap((tile) => tile.premises.map((premise) => premise.id))).size).toBe(model.premises.length);
  const coreLabel = report.items[0]?.statement_id;
  if (coreLabel) {
    const focused = buildAtlasModel(getCorpus(), report, [coreLabel]);
    expect(Object.keys(focused.labels)).toEqual([coreLabel]);
  }
  for (const route of model.routes) {
    expect(route.bare + route.sourced + route.provedUnestablished).toBe(route.open_premise_statement_ids.length);
    expect(route.cost).toBe(route.open_premise_statement_ids.length);
    for (const premise of route.open_premise_statement_ids) {
      expect(routeImpact(route, premise)).toBe(true);
    }
    expect(model.argumentTargets[route.argument_id]).toMatch(/^\/(results|statements)\//);
  }
  for (const premise of model.premises) {
    for (const argumentId of premise.dependentArguments) {
      expect(model.argumentTargets[argumentId]).toMatch(/^\/(results|statements)\//);
    }
  }
}, 30000);

test("mosaic enumerates exact certified terminal status in Gray order without inferring new proof status", () => {
  const cells = certifiedMosaic(fixture());
  expect(cells.map((cell) => cell.mask)).toEqual([0, 1, 3, 2]);
  expect(cells.map((cell) => cell.status)).toEqual(["model witnessed", "verified incompatible", "verified incompatible", "model witnessed"]);
  expect(cells[0]?.modelId).toBe("M");
  expect(cells[1]?.resultId).toBe("R");
  expect(certifiedCores(fixture())).toHaveLength(1);
  expect(certifiedCores(fixture())[0]?.statement_ids).toEqual(["P", "Q"]);
});

test("broken certified assumption path fails closed instead of showing unresolved as if certified", () => {
  const configuration = fixture();
  configuration.assumption_space.nodes = configuration.assumption_space.nodes.filter((node) => node.id !== "impossible");
  expect(() => certifiedMosaic(configuration)).toThrow("Invalid certified configuration");
});
