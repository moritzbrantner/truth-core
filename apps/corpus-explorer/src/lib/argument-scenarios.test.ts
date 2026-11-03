import { describe, expect, test } from "bun:test";

import { buildArgumentForest } from "./argument-forest";
import { exploreAssumptions } from "./argument-scenarios";
import { fixtureGraph } from "./frontier-fixture";
import { fixture } from "./proposition-graph.fixture";

const graph = fixtureGraph(fixture);
const model = buildArgumentForest(graph, [{ id: "ROOT", label: "Root" }], { exhaustive: true });

describe("hypothetical assumption exploration", () => {
  test("requires all premises, then carries implications through multiple argument levels", () => {
    const partial = exploreAssumptions(model, ["P1", "P2"], []);
    expect(partial.derived.get("C")).toEqual(["A1"]);
    expect(partial.reachable.has("ROOT")).toBe(false);

    const complete = exploreAssumptions(model, ["P1", "P2", "SE", "DEF"], []);
    expect(complete.derived.get("C")).toEqual(["A1"]);
    expect(complete.derived.get("ROOT")).toEqual(["A2"]);
    expect(complete.accepted.has("C")).toBe(false);
    expect(model.statements.C.status).toBe(graph.statements.find((entry) => entry.id === "C")?.established ? "established" : "conditional");
  });

  test("records conflicts but does not use denied conclusions to derive other claims", () => {
    const scenario = exploreAssumptions(model, ["P1", "P2", "SE", "DEF"], ["ROOT"]);
    expect(scenario.conflicts.get("ROOT")).toEqual(["A2"]);
    expect(scenario.reachable.has("ROOT")).toBe(false);
    expect(scenario.denied.has("ROOT")).toBe(true);
  });

  test("does not promote research links, result-free arguments or zero-premise results", () => {
    const empty = exploreAssumptions(model, [], []);
    expect(empty.derived.size).toBe(0);
    expect(empty.reachable.has("NALT")).toBe(false);
    const withResearch = exploreAssumptions(model, ["ALT"], []);
    expect(withResearch.derived.has("OBJ")).toBe(false);
    expect(withResearch.derived.has("DEF")).toBe(false);
    const withTranscription = exploreAssumptions(model, ["T"], []);
    expect(withTranscription.derived.get("TC")).toEqual(["A4"]);
    expect(withTranscription.derived.has("TOP")).toBe(false);
  });

  test("retains alternative recorded routes and terminates on shared cycles", () => {
    const alternate = {
      ...model,
      arguments: {
        ...model.arguments,
        OTHER: { ...model.arguments.A1, id: "OTHER", premises: ["SE"] },
        CYCLE: { ...model.arguments.A1, id: "CYCLE", conclusion: "P1", premises: ["C"] },
      },
    };
    const scenario = exploreAssumptions(alternate, ["P1", "P2", "SE"], []);
    expect(scenario.derived.get("C")).toEqual(["A1", "OTHER"]);
    expect(scenario.reachable.size).toBe(4);
    expect(scenario.derived.has("P1")).toBe(false);
  });
});
