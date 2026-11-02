import { describe, expect, test } from "bun:test";

import type { ForestArgument } from "./argument-forest";
import { buildArgumentForest } from "./argument-forest";
import { orderArgumentRoutes } from "./argument-route-order";
import { exploreAssumptions } from "./argument-scenarios";
import { fixtureGraph } from "./frontier-fixture";
import { fixture } from "./proposition-graph.fixture";

const model = buildArgumentForest(fixtureGraph(fixture), [{ id: "ROOT", label: "Root" }], { exhaustive: true });

function route(id: string, premises: string[], resultIds = ["R1"], transcriptionOnly = false): ForestArgument {
  return { id, conclusion: "ROOT", meaning: id, premises, resultIds, transcriptionOnly };
}

const routes = [
  route("UNLISTED", [], ["R6"]),
  route("BLOCKED", ["P1", "DEF"]),
  route("NEEDS_TWO", ["P1", "SE", "T"]),
  route("NEEDS_ONE", ["P1", "SE"]),
  route("READY_NO_RESULT", ["P1", "P2"], []),
  route("READY_TRANSCRIPTION", ["P1", "P2"], ["R4"], true),
  route("READY_RESULT", ["P1", "C"]),
];

describe("belief-aware argument route ordering", () => {
  test("prioritizes reached premises, then missing premises, then denials without hiding routes", () => {
    // P1 and P2 also reach C through an independent recorded argument.
    const scenario = exploreAssumptions(model, ["P1", "P2"], ["DEF"]);
    const ordered = orderArgumentRoutes(routes, scenario);
    expect(ordered.map((entry) => entry.argument.id)).toEqual([
      "READY_RESULT", "READY_TRANSCRIPTION", "READY_NO_RESULT",
      "NEEDS_ONE", "NEEDS_TWO", "BLOCKED", "UNLISTED",
    ]);
    expect(ordered.map((entry) => entry.readiness)).toEqual([
      "reached", "reached", "reached", "needs", "needs", "blocked", "unlisted",
    ]);
    expect(ordered.find((entry) => entry.argument.id === "NEEDS_ONE")?.missing).toEqual(["SE"]);
    expect(ordered.find((entry) => entry.argument.id === "BLOCKED")?.denied).toEqual(["DEF"]);
    // A result-free route is still displayed as premises-met, never promoted to a proof.
    expect(ordered.find((entry) => entry.argument.id === "READY_NO_RESULT")?.argument.resultIds).toEqual([]);
  });

  test("deduplicates repeated premises for readiness, but preserves the argument's AND record", () => {
    const scenario = exploreAssumptions(model, ["P1"], []);
    const [entry] = orderArgumentRoutes([route("DUPLICATED", ["P1", "P1", "SE"])], scenario);
    expect(entry.totalCount).toBe(2);
    expect(entry.reachedCount).toBe(1);
    expect(entry.missing).toEqual(["SE"]);
    expect(entry.argument.premises).toEqual(["P1", "P1", "SE"]);
  });

  test("reorders when a needed premise is accepted, but does not auto-activate a zero-premise result", () => {
    const scenario = exploreAssumptions(model, ["P1", "P2", "SE", "DEF"], []);
    const ordered = orderArgumentRoutes(routes, scenario);
    expect(ordered.find((entry) => entry.argument.id === "NEEDS_ONE")?.readiness).toBe("reached");
    expect(ordered.find((entry) => entry.argument.id === "BLOCKED")?.readiness).toBe("reached");
    expect(ordered.at(-1)?.argument.id).toBe("UNLISTED");
    expect(ordered.at(-1)?.readiness).toBe("unlisted");
  });

  test("supports explicit shortest and corpus orders without modifying recorded arguments", () => {
    const scenario = exploreAssumptions(model, ["P1", "P2"], ["DEF"]);
    expect(orderArgumentRoutes(routes, scenario, "recorded").map((entry) => entry.argument.id))
      .toEqual(routes.map((entry) => entry.id));
    const shortest = orderArgumentRoutes(routes, scenario, "shortest");
    expect(shortest[0].totalCount).toBe(2);
    expect(shortest.at(-1)?.argument.id).toBe("UNLISTED");
    expect(routes[0].id).toBe("UNLISTED");
  });
});
