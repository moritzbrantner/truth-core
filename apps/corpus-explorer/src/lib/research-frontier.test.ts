import { expect, test } from "bun:test";
import { getCorpus } from "./corpus";
import { getPropositionGraph } from "./proposition-graph-data";
import { getFrontierReport } from "./site-state";
import { orderObligations, researchFrontier } from "./research-frontier";
import { fixtureGraph, fixtureReport } from "./frontier-fixture";
import { fixture } from "./proposition-graph.fixture";
import { parseGraphState, serializeGraphState, DEFAULT_STATE } from "./graph-state";
import { computeGraphView } from "./graph-view";

const corpus = getCorpus();
const graph = getPropositionGraph(corpus);
const report = getFrontierReport();
const obligations = researchFrontier(corpus, graph, report);
const options = { target: "", selected: "", pins: [], kind: "" };

test("graph closed/established/open distinction and queue derive exactly from Python", () => {
  expect(
    obligations
      .filter((item) => item.kind === "derivation")
      .map((item) => item.statementIds[0])
      .sort(),
  ).toEqual(report.items.map((item) => item.statement_id).sort());
  expect(
    graph.statements
      .filter((item) => item.established)
      .map((item) => item.id)
      .sort(),
  ).toEqual(report.established_statements);
  expect(
    graph.statements
      .filter((item) => item.closureReason)
      .map((item) => item.id)
      .sort(),
  ).toEqual(Object.keys(report.closed_statements).sort());
  expect(graph.statements.find((item) => item.id === report.root)).toMatchObject({
    established: false,
    closureReason: "proved",
  });
  expect(new Set(obligations.map((item) => item.id)).size).toBe(obligations.length);
  for (const item of obligations.filter((entry) => entry.kind === "derivation" || entry.kind === "evidence")) {
    expect(item.href).toBe(`/dossiers/${item.statementIds[0]}`);
  }
});

test("global vs goal scope follows route-aware authoritative dependents", () => {
  const global = orderObligations(obligations, options);
  const scoped = orderObligations(obligations, {
    ...options,
    target: report.root,
  });
  expect(scoped.length).toBeLessThan(global.length);
  expect(
    scoped
      .filter((item) => item.kind === "derivation")
      .map((item) => item.statementIds[0])
      .sort(),
  ).toEqual(
    report.items
      .filter((item) => item.path_to_root !== null)
      .map((item) => item.statement_id)
      .sort(),
  );
  const item = scoped[0];
  expect(
    orderObligations(obligations, {
      ...options,
      selected: item.statementIds[0],
    })[0].statementIds,
  ).toContain(item.statementIds[0]);
  expect(orderObligations(obligations, { ...options, pins: [global.at(-1)!.id] })[0].id).toBe(global.at(-1)!.id);
});

test("URL restores selected obligation, goal, pins, expansion, filters and focus return", () => {
  const state = {
    ...DEFAULT_STATE,
    scope: "goal" as const,
    target: report.root,
    obligation: obligations[0].id,
    pins: [obligations[0].id],
    expanded: [report.root],
    sel: report.root,
    kind: "evidence",
    returnView: "view=all&sel=OLD",
  };
  expect(parseGraphState(new URLSearchParams(serializeGraphState(state)))).toEqual(state);
});

test("reciprocal implication cycles are conditional until an established input enters", () => {
  const cyclic = structuredClone(fixture);
  cyclic.arguments = [
    {
      id: "AB",
      premise_statement_ids: ["P1"],
      conclusion_statement_id: "P2",
      inference_ids: ["AB-I"],
      meaning: "A to B",
    },
    {
      id: "BA",
      premise_statement_ids: ["P2"],
      conclusion_statement_id: "P1",
      inference_ids: ["BA-I"],
      meaning: "B to A",
    },
  ];
  cyclic.inferences = cyclic.arguments.map((argument) => ({
    id: argument.inference_ids[0],
    input_statement_ids: argument.premise_statement_ids,
    output_statement_id: argument.conclusion_statement_id,
    rule: "implication",
    meaning: "Conditional",
  }));
  cyclic.results = [
    { id: "AB-R", argument_id: "AB" },
    { id: "BA-R", argument_id: "BA" },
  ];
  cyclic.transcriptionResultIds = [];
  expect(fixtureReport(cyclic).established_statements).not.toContain("P1");
  const g = fixtureGraph(cyclic);
  const view = computeGraphView(g, {
    ...DEFAULT_STATE,
    view: "focus",
    node: "P1",
    hops: 6,
    expanded: ["P1", "P2"],
  });
  expect(
    view.nodes
      .filter((node) => node.kind === "statement")
      .map((node) => node.id)
      .sort(),
  ).toEqual(["P1", "P2"]);
  cyclic.statements.find((item) => item.id === "P1")!.self_evident = {
    justification_ids: ["CL-P1-A"],
  };
  expect(fixtureReport(cyclic).established_statements).toContain("P2");
});

test("status update removes resolved obligations and interpretation split adds exploration", () => {
  const open = report.items[0];
  const closed = {
    ...report,
    items: report.items.filter((item) => item !== open),
    closed_statements: {
      ...report.closed_statements,
      [open.statement_id]: "proved" as const,
    },
  };
  expect(researchFrontier(corpus, graph, closed).some((item) => item.id === `derivation:${open.statement_id}`)).toBe(
    false,
  );
  const split = {
    ...corpus,
    claims: [...corpus.claims, { ...corpus.claims[0], id: "CL-TEST-SPLIT", interpretation_of: corpus.claims[1].id }],
  };
  const afterSplit = researchFrontier(split, graph, report);
  expect(afterSplit.length).toBe(obligations.length + 1);
  expect(afterSplit.find((item) => item.id === "interpretation:CL-TEST-SPLIT")?.recordIds).toEqual([
    "CL-TEST-SPLIT",
    corpus.claims[1].id,
  ]);
  expect(obligations.some((item) => item.kind === "interpretation")).toBe(true);
  expect(obligations.some((item) => item.frontier === "exploration")).toBe(true);
});

test("global projection clusters large corpus instead of mounting every statement", () => {
  const view = computeGraphView(graph, { ...DEFAULT_STATE, layout: "layered" });
  expect(graph.statements.length).toBeGreaterThan(900);
  expect(view.nodes.length).toBeLessThan(graph.statements.length);
  expect(new Set(view.nodes.map((node) => node.id)).size).toBe(view.nodes.length);
});

test("in-place expansion opens adjacent clusters while retaining shared identity", () => {
  const g = fixtureGraph(fixture);
  const initial = computeGraphView(g, { ...DEFAULT_STATE, layout: "layered" });
  const expanded = computeGraphView(g, { ...DEFAULT_STATE, layout: "layered", expanded: ["P1"] });
  expect(expanded.nodes.filter((node) => node.kind === "statement").length).toBeGreaterThan(
    initial.nodes.filter((node) => node.kind === "statement").length,
  );
  expect(expanded.nodes.some((node) => node.id === "I1")).toBe(true);
  expect(new Set(expanded.nodes.map((node) => node.id)).size).toBe(expanded.nodes.length);
});


test("candidate gaps reference complete statement IDs rather than name prefixes", () => {
  const referenceGraph = {
    ...graph,
    statements: [
      { ...graph.statements[0], id: "STMT-PREFIX" },
      { ...graph.statements[0], id: "STMT-PREFIX-LONG" },
    ],
  };
  const entries = researchFrontier({
    ...corpus,
    candidates: [{
      id: "EXACT-REFERENCE", source_id: "SRC", locator: "1", priority: 1,
      goal: "Investigate STMT-PREFIX-LONG.", reason: "A queued reading, not a naming equivalence.", status: "candidate",
    }],
  }, referenceGraph, report);
  expect(entries.find((item) => item.id === "exploration:EXACT-REFERENCE")?.statementIds).toEqual(["STMT-PREFIX-LONG"]);
});
