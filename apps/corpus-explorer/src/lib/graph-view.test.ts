import { fixtureGraph } from "./frontier-fixture";
import { describe, expect, test } from "bun:test";

import { DEFAULT_STATE, type GraphState } from "./graph-state";
import { computeGraphView, indexGraph, searchStatements } from "./graph-view";

import { getPropositionGraph } from "./proposition-graph-data";
import { fixture } from "./proposition-graph.fixture";

const graph = fixtureGraph(fixture);
const state = (patch: Partial<GraphState>): GraphState => ({ ...DEFAULT_STATE, view: "root", ...patch });
const ids = (view: ReturnType<typeof computeGraphView>, kind?: string) =>
  view.nodes.filter((node) => !kind || node.kind === kind).map((node) => node.id).sort();

describe("graph views", () => {
  test("root-path view shows everything the target rests on, through inference nodes", () => {
    const view = computeGraphView(graph, state({}));
    expect(view.anchor).toBe("ROOT");
    expect(ids(view, "statement")).toEqual(["C", "DEF", "P1", "P2", "ROOT", "SE"]);
    expect(ids(view, "inference")).toEqual(["I1", "I2"]);
    expect(view.frontierCount).toBe(2);
  });

  test("never draws a bare statement-to-statement support edge", () => {
    const view = computeGraphView(graph, state({ view: "all", open: ["SRC-1", "derived · TruthCore.Test"] }));
    const kinds = new Map(view.nodes.map((node) => [node.id, node.kind]));
    for (const edge of view.edges) {
      if (edge.kind === "relation" || edge.kind === "cluster") continue;
      expect([kinds.get(edge.source), kinds.get(edge.target)]).toContain("inference");
    }
  });

  test("focus mode walks N hops up or down and keeps every premise of a step", () => {
    const up = computeGraphView(graph, state({ view: "focus", node: "P1", hops: 1, dir: "up" }));
    expect(ids(up, "statement")).toEqual(["C", "P1", "P2"]);
    const upTwo = computeGraphView(graph, state({ view: "focus", node: "P1", hops: 2, dir: "up" }));
    expect(ids(upTwo, "statement")).toEqual(["C", "DEF", "P1", "P2", "ROOT", "SE"]);
    const down = computeGraphView(graph, state({ view: "focus", node: "ROOT", hops: 1, dir: "down" }));
    expect(ids(down, "inference")).toEqual(["I2"]);
    expect(ids(down, "statement")).toEqual(["C", "DEF", "ROOT", "SE"]);
    const inference = computeGraphView(graph, state({ view: "focus", node: "I1", hops: 1 }));
    expect(ids(inference, "statement")).toEqual(["C", "P1", "P2"]);
  });

  test("filters dim by default and hide on request", () => {
    const dimmed = computeGraphView(graph, state({ status: ["open"] }));
    const matched = dimmed.nodes.filter((node) => node.kind === "statement" && node.matched).map((node) => node.id);
    expect(matched.sort()).toEqual(["P1", "P2"]);
    const hidden = computeGraphView(graph, state({ status: ["open"], hide: true }));
    // The anchor stays; steps lose their nodes once their conclusion or all premises are hidden.
    expect(ids(hidden, "statement")).toEqual(["P1", "P2", "ROOT"]);
    expect(ids(hidden, "inference")).toEqual([]);
  });

  test("hiding keeps every premise of a drawn step", () => {
    const view = computeGraphView(graph, state({ view: "focus", node: "C", hops: 1, dir: "down", q: "P1", hide: true }));
    expect(ids(view, "statement")).toEqual(["C", "P1", "P2"]);
    expect(ids(view, "inference")).toEqual(["I1"]);
    const p2 = view.nodes.find((node) => node.id === "P2");
    expect(p2?.kind === "statement" && p2.matched).toBe(false);
  });

  test("full view clusters statements and summarizes steps into collapsed clusters", () => {
    const collapsed = computeGraphView(graph, state({ view: "all" }));
    expect(collapsed.nodes.every((node) => node.kind === "cluster")).toBe(true);
    const expanded = computeGraphView(graph, state({ view: "all", open: ["derived · TruthCore.Test"] }));
    expect(ids(expanded, "inference")).toContain("I1");
    expect(expanded.edges.some((edge) => edge.source === "cluster:SRC-1" && edge.target === "I1")).toBe(true);
    const summary = computeGraphView(graph, state({ view: "all", open: [] })).edges.find(
      (edge) => edge.source === "cluster:SRC-1",
    );
    expect(summary?.label).toBe("1 step");
  });

  test("relations are drawn as their own edge kind between visible statements", () => {
    const view = computeGraphView(graph, state({ view: "focus", node: "A3-unknown" }));
    expect(view.nodes).toHaveLength(0);
    const focus = computeGraphView(graph, state({ view: "focus", node: "OBJ", hops: 1, dir: "down" }));
    expect(focus.edges.filter((edge) => edge.kind === "relation")).toHaveLength(0);
    const all = computeGraphView(graph, state({ view: "all", open: ["derived · TruthCore.Test"] }));
    expect(all.edges.filter((edge) => edge.kind === "relation").map((edge) => edge.label)).toEqual([
      "alternative to",
      "attacks",
    ]);
  });

  test("search ranks frontier statements first", () => {
    const result = searchStatements(graph, state({ q: "paraphrase" }), 3);
    expect(result.total).toBe(12);
    expect(result.items.every((item) => item.frontier)).toBe(true);
  });
});

describe("corpus graph views", () => {
  const corpusGraph = getPropositionGraph();
  const index = indexGraph(corpusGraph);

  test("the default root-path view is a bounded subgraph", () => {
    const view = computeGraphView(corpusGraph, { ...DEFAULT_STATE, view: "root" }, index);
    expect(view.statementCount).toBeGreaterThan(1);
    expect(view.statementCount).toBeLessThan(corpusGraph.statements.length);
    expect(view.nodes.some((node) => node.kind === "inference")).toBe(true);
  });

  test("the collapsed full graph stays small", () => {
    const view = computeGraphView(corpusGraph, state({ view: "all" }), index);
    expect(view.nodes.length).toBeLessThan(200);
    expect(view.statementCount).toBe(corpusGraph.statements.length);
  });
});
