import { describe, expect, test } from "bun:test";

import { buildAssumptionTree, type ForestTreeModel } from "./argument-forest";
import { buildAssumptionRelevance, rankImplications, rankPropositionMatches, sortAssumptionArguments } from "./assumption-relevance";
import { exploreAssumptions } from "./argument-scenarios";
import { fixtureGraph } from "./frontier-fixture";
import { fixture } from "./proposition-graph.fixture";

const model = buildAssumptionTree(fixtureGraph(fixture));

describe("assumption explorer relevance", () => {
  test("places goal-path and actionable proposition matches ahead of unrelated corpus enumeration", () => {
    const scenario = exploreAssumptions(model, ["P1", "P2", "SE"], []);
    const relevance = buildAssumptionRelevance(model, "ROOT", scenario);
    expect(relevance.goalDistance.get("ROOT")).toBe(0);
    expect(relevance.goalDistance.get("C")).toBe(1);
    expect(relevance.goalDistance.get("P1")).toBe(2);
    expect(relevance.goalDistance.has("LONE")).toBe(false);
    expect(relevance.completesGoalRoute.has("DEF")).toBe(true);
    expect(rankPropositionMatches(model, "paraphrase", relevance, scenario).slice(0, 3).map((entry) => entry.id))
      .toEqual(["DEF", "ROOT", "C"]);
    expect(rankPropositionMatches(model, "def", relevance, scenario)[0]?.id).toBe("DEF");
    expect(rankPropositionMatches(model, "root paraphrase", relevance, scenario)[0]?.id).toBe("ROOT");
    expect(rankPropositionMatches(model, "p1 paraphrase", relevance, scenario)[0]?.id).toBe("P1");
    expect(rankPropositionMatches(model, "p1 missing", relevance, scenario)).toEqual([]);
  });

  test("orders result routes by scenario readiness, then by unresolved and contradicted premises", () => {
    const multi: ForestTreeModel = {
      ...model,
      statements: {
        ...model.statements,
        ROOT: { ...model.statements.ROOT, argumentIds: ["BLOCKED", "NO_RESULT", "WAITING", "READY", "TRANSCRIPTION", "WAITING_SUPPORT"] },
      },
      arguments: {
        ...model.arguments,
        READY: { ...model.arguments.A2, id: "READY", premises: ["P1", "P2"] },
        WAITING: { ...model.arguments.A2, id: "WAITING", premises: ["P1", "DEF"] },
        WAITING_SUPPORT: { ...model.arguments.A2, id: "WAITING_SUPPORT", premises: ["P1", "TC"] },
        BLOCKED: { ...model.arguments.A2, id: "BLOCKED", premises: ["P1", "ALT"] },
        NO_RESULT: { ...model.arguments.A2, id: "NO_RESULT", premises: ["P1"], resultIds: [] },
        TRANSCRIPTION: { ...model.arguments.A2, id: "TRANSCRIPTION", premises: ["P1", "P2"], transcriptionOnly: true },
      },
    };
    const scenario = exploreAssumptions(multi, ["P1", "P2"], ["ALT"]);
    const relevance = buildAssumptionRelevance(multi, "ROOT", scenario);
    expect(sortAssumptionArguments(multi.statements.ROOT.argumentIds, relevance)).toEqual([
      "READY", "TRANSCRIPTION", "WAITING_SUPPORT", "WAITING", "NO_RESULT", "BLOCKED",
    ]);
    expect(relevance.routeReadiness.get("WAITING")).toMatchObject({ satisfied: 1, unresolved: 1, contradicted: 0 });
    expect(relevance.routeReadiness.get("WAITING_SUPPORT")?.unresolvedWithSupport).toBe(1);
    expect(relevance.routeReadiness.get("BLOCKED")).toMatchObject({ satisfied: 1, unresolved: 0, contradicted: 1 });
    expect(relevance.routeReadiness.get("NO_RESULT")?.applicable).toBe(false);
  });

  test("ranks implications by usefulness to the goal without changing certified reachability", () => {
    const scenario = exploreAssumptions(model, ["P1", "P2", "SE", "DEF", "T"], []);
    const relevance = buildAssumptionRelevance(model, "ROOT", scenario);
    expect(rankImplications(scenario.derived, relevance).map(([id]) => id)).toEqual(["ROOT", "C", "TC"]);
    expect(scenario.derived.get("ROOT")).toEqual(["A2"]);
    expect(model.statements.ROOT.status).not.toBe("established");
  });

  test("handles thousands of propositions, shared dependencies and cycles with deterministic ordering", () => {
    const size = 2200;
    const statements = Object.fromEntries(Array.from({ length: size }, (_, index) => {
      const id = `N${index}`;
      return [id, { id, paraphrase: `Proposition ${index}`, status: "open" as const,
        statusLabel: "Open premise", argumentIds: index ? [`R${index}`] : [], totalArguments: index ? 1 : 0 }];
    }));
    const argumentsMap = Object.fromEntries(Array.from({ length: size - 1 }, (_, offset) => {
      const index = offset + 1;
      const id = `R${index}`;
      return [id, { id, conclusion: `N${index}`, meaning: "Step", premises: [`N${index - 1}`, "N0"],
        resultIds: [id], transcriptionOnly: false }];
    }));
    const full: ForestTreeModel = {
      defaultGoal: `N${size - 1}`, statements, arguments: {
        ...argumentsMap,
        CYCLE: { id: "CYCLE", conclusion: "N0", meaning: "Cycle", premises: [`N${size - 1}`], resultIds: [], transcriptionOnly: false },
      },
    };
    full.statements.N0.argumentIds.push("CYCLE");
    const scenario = exploreAssumptions(full, ["N0"], []);
    const relevance = buildAssumptionRelevance(full, full.defaultGoal, scenario);
    expect(relevance.goalDistance.size).toBe(size);
    expect(relevance.goalDistance.get("N0")).toBe(1);
    const results = rankPropositionMatches(full, "proposition", relevance, scenario, size);
    expect(results).toHaveLength(size);
    expect(results[0].id).toBe(full.defaultGoal);
    expect(results.map((entry) => entry.id)).toEqual(rankPropositionMatches(full, "proposition", relevance, scenario, size).map((entry) => entry.id));
  });
});
