import { describe, expect, test } from "bun:test";

import { buildArgumentForest, buildAssumptionTree, TREE_MEANING_LIMIT } from "./argument-forest";
import { fixtureGraph } from "./frontier-fixture";
import { fixture } from "./proposition-graph.fixture";

const roots = [
  { id: "ROOT", label: "Root conclusion" },
  { id: "DEF", label: "Alternative" },
  { id: "TC", label: "Transcribed result" },
];

describe("argument forest projection", () => {
  const graph = fixtureGraph(fixture);
  const model = buildArgumentForest(graph, roots);

  test("preserves OR argument routes and AND premise membership, with stable statement identity", () => {
    expect(model.defaultGoal).toBe("ROOT");
    expect(model.defaultCompare).toBe("DEF");
    expect(model.statements.ROOT.argumentIds).toContain("A2");
    expect(model.arguments.A2.premises).toEqual(["C", "SE", "DEF"]);
    expect(model.statements.C.argumentIds).toContain("A1");
    expect(model.arguments.A1.premises).toEqual(["P1", "P2"]);
    expect(Object.keys(model.statements).filter((id) => id === "P1")).toHaveLength(1);
    expect(model.arguments.A2.resultIds).toEqual(["R2"]);
  });

  test("marks recorded rival research links but never fabricates a negated proposition", () => {
    expect(model.statements.DEF.rivals).toEqual(expect.arrayContaining([
      expect.objectContaining({ id: "ALT", predicate: "alternative_to" }),
    ]));
    expect(model.statements.P1.rivals).toHaveLength(0);
    expect(Object.keys(model.statements).every((id) => !id.startsWith("¬"))).toBe(true);
  });

  test("only reports dependency reach and the corpus-owned status", () => {
    expect(model.statements.P1.directConsequences.map((entry) => entry.id)).toContain("C");
    expect(model.statements.ROOT.directConsequences).toEqual([]);
    expect(model.statements.P1.status).toBe(graph.statements.find((entry) => entry.id === "P1")?.frontier ? "open" : "other");
    // A transcription with open premises remains on the frontier despite its recorded result.
    expect(model.statements.TC.statusLabel).toBe("Open premise");
    expect(model.arguments.A4.transcriptionOnly).toBe(true);
  });

  test("terminates with shared statements and cyclic argument references", () => {
    const cyclic = { ...graph, arguments: [
      ...graph.arguments,
      { ...graph.arguments[0], id: "LOOP", conclusion: "P1", premises: ["ROOT"], resultIds: [], transcriptionResultIds: [] },
    ] };
    const projected = buildArgumentForest(cyclic, roots);
    expect(projected.statements.ROOT).toBeDefined();
    expect(projected.statements.P1).toBeDefined();
    expect(Object.keys(projected.statements).length).toBeLessThanOrEqual(graph.statements.length);
  });

  test("exhaustive exploration includes every proposition and argument, including routes beyond the two-route overview", () => {
    const expandedGraph = {
      ...graph,
      arguments: [
        ...graph.arguments,
        { ...graph.arguments[0], id: "A7", conclusion: "ROOT", premises: ["P1", "P2", "TC", "TOP"] },
        { ...graph.arguments[0], id: "A8", conclusion: "ROOT", premises: ["ALT"] },
        { ...graph.arguments[0], id: "A9", conclusion: "P1", premises: ["ROOT"] },
      ],
    };
    const complete = buildArgumentForest(expandedGraph, roots, { exhaustive: true });
    expect(Object.keys(complete.statements).length).toBe(graph.statements.length);
    expect(complete.statements.ROOT.argumentIds).toEqual(expect.arrayContaining(["A2", "A7", "A8"]));
    expect(complete.arguments.A7.premises).toEqual(["P1", "P2", "TC", "TOP"]);
    expect(complete.statements.P1.argumentIds).toContain("A9");
    expect(complete.arguments.A9.conclusion).toBe("P1");
    expect(model.statements.ROOT.argumentIds).toEqual(["A2"]);
  });

  test("single-tree payload omits comparison metadata while preserving every recorded argument", () => {
    const compact = buildAssumptionTree(graph);
    expect(Object.keys(compact.statements)).toHaveLength(graph.statements.length);
    expect(Object.keys(compact.arguments)).toHaveLength(graph.arguments.length);
    expect(compact.statements.ROOT.argumentIds).toContain("A2");
    expect(compact.statements.ROOT).not.toHaveProperty("rivals");
    expect(compact.statements.ROOT).not.toHaveProperty("directConsequences");
    for (const argument of Object.values(compact.arguments)) {
      expect(argument.meaning.length).toBeLessThanOrEqual(TREE_MEANING_LIMIT + 1);
    }
  });

  test("chooses a known fallback root rather than inventing evidence", () => {
    const projected = buildArgumentForest(graph, [{ id: "NOT-IN-CORPUS", label: "Missing" }]);
    expect(projected.roots.some((root) => root.id === "NOT-IN-CORPUS")).toBe(false);
    expect(graph.statements.some((statement) => statement.id === projected.defaultGoal)).toBe(true);
  });
});
