import { fixtureGraph } from "./frontier-fixture";
import { describe, expect, test } from "bun:test";

import { DEFAULT_STATE, type GraphState } from "./graph-state";
import { computeGraphView, indexGraph, searchStatements } from "./graph-view";

import { getPropositionGraph } from "./proposition-graph-data";
import { fixture } from "./proposition-graph.fixture";

const graph = fixtureGraph(fixture);
const state = (patch: Partial<GraphState>): GraphState => ({ ...DEFAULT_STATE, view: "root", layout: "layered", ...patch });
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
    const all = computeGraphView(graph, state({ view: "all", relations: true, open: ["derived · TruthCore.Test"] }));
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

  test("growing two collapsed groups keeps two nodes and summarizes their inference", () => {
    const statement = graph.statements[0];
    const inference = graph.inferences[0];
    if (!statement || !inference) throw new Error("The graph fixture needs a statement and inference");
    const grown = {
      ...graph,
      statements: Array.from({ length: 2000 }, (_, i) => ({
        ...statement,
        id: `GROW-${i}`,
        clusters: { ...statement.clusters, passage: i < 1000 ? "GROW-A" : "GROW-B" },
      })),
      inferences: [{ ...inference, id: "GROW-I", inputs: ["GROW-0"], assumptions: [], output: "GROW-1999" }],
      relations: [],
    };
    const view = computeGraphView(grown, state({ view: "all" }));
    expect(view.nodes.map((node) => node.kind)).toEqual(["cluster", "cluster"]);
    expect(view.nodes.filter((node) => node.kind === "cluster").map((node) => [node.key, node.size]))
      .toEqual([["GROW-A", 1000], ["GROW-B", 1000]]);
    expect(view.statementCount).toBe(2000);
    expect(view.edges.map((edge) => [edge.source, edge.target, edge.kind, edge.label]))
      .toEqual([["cluster:GROW-A", "cluster:GROW-B", "cluster", "1 step"]]);
  });

  test("the collapsed full graph scales with groups and retains every statement", () => {
    for (const cluster of ["passage", "source", "namespace"] as const) {
      const view = computeGraphView(corpusGraph, state({ view: "all", cluster }), index);
      const groupSizes = new Map<string, number>();
      for (const statement of corpusGraph.statements) {
        const key = statement.clusters[cluster];
        groupSizes.set(key, (groupSizes.get(key) ?? 0) + 1);
      }
      const clusters = view.nodes.filter((node) => node.kind === "cluster");
      expect(clusters.length).toBe(view.nodes.length);
      expect(clusters.map((node) => node.key).sort()).toEqual([...groupSizes.keys()].sort());
      for (const node of clusters) {
        expect(node.size).toBe(groupSizes.get(node.key));
      }
      expect(clusters.reduce((sum, node) => sum + node.size, 0)).toBe(corpusGraph.statements.length);
      expect(view.statementCount).toBe(corpusGraph.statements.length);
      // Retain at least a fivefold reduction without freezing the number of source ranges.
      expect(view.nodes.length * 5).toBeLessThanOrEqual(corpusGraph.statements.length);
    }
  });
});
