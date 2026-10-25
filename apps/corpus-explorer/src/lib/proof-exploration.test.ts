import { expect, test } from "bun:test";
import { fixtureGraph } from "./frontier-fixture";
import type { PropositionGraphInput } from "./proposition-graph";
import { exploreProof, runProofExploration } from "./proof-exploration";

function input(edges: [string, string[], string][], seeds = ["A"]): PropositionGraphInput {
  const ids = [...new Set([...seeds, ...edges.flatMap(([, from, to]) => [...from, to])])];
  return {
    statements: ids.map((id) => ({ id, paraphrase: id, ...(seeds.includes(id) ? { self_evident: { justification_ids: [`CL-${id}`] } } : {}) })),
    claims: seeds.map((id) => ({ id: `CL-${id}`, statement_id: id, source_id: "S", locator: "1", interpretation: "Fixture ground only." })),
    sources: [{ id: "S", author: "Fixture", work: "Synthetic" }],
    inferences: edges.map(([id, from, to]) => ({ id: `I-${id}`, input_statement_ids: from, output_statement_id: to, rule: "fixture", meaning: "Fixture step." })),
    arguments: edges.map(([id, from, to]) => ({ id, premise_statement_ids: from, conclusion_statement_id: to, inference_ids: [`I-${id}`], meaning: "Fixture conditional." })),
    results: edges.map(([id]) => ({ id: `R-${id}`, argument_id: id })),
    // Flag opaque fixture conditionals as transcriptions. Without grounding,
    // their checked consequence alone must not establish a fact.
    transcriptionResultIds: edges.map(([id]) => `R-${id}`),
    relations: [],
  };
}

test("exact-ID reuse traverses actual intermediate and preserves proposed status", () => {
  const graph = fixtureGraph(input([["AB", ["A"], "B"], ["BC", ["B"], "C"]]));
  const result = runProofExploration(graph, { target: "C", scope: ["A"], budget: 100 });
  expect(result.status).toBe("complete");
  expect(result.establishedStatementIds).toEqual(["A"]);
  expect(result.forwardStatementIds).toEqual(["A", "B", "C"]);
  expect(result.backwardStatementIds).toEqual(["A", "B", "C"]);
  expect(result.joins.find((j) => j.statementId === "C")).toEqual({ statementId: "C", status: "proposed", argumentIds: ["AB", "BC"], remainingStatementIds: [] });
});

test("AND retains every blocker and OR offers an independent route", () => {
  const data = input([["AND", ["A", "B"], "C"]]);
  const partial = runProofExploration(fixtureGraph(data), { target: "C", budget: 100 });
  expect(partial.forwardStatementIds).toEqual(["A"]);
  expect(partial.branches[0].remainingStatementIds).toEqual(["B"]);
  expect(partial.joins[0].remainingStatementIds).toEqual(["B"]);
  const alternate = runProofExploration(fixtureGraph(input([["AND", ["A", "B"], "C"], ["OR", ["A"], "C"]])), { target: "C", budget: 100 });
  expect(alternate.forwardStatementIds).toContain("C");
  expect(alternate.branches.find((b) => b.inferenceId === "I-OR")?.remainingStatementIds).toEqual([]);
  expect(alternate.branches.find((b) => b.inferenceId === "I-AND")?.remainingStatementIds).toEqual(["B"]);
});

test("ungrounded cycles, unchecked inferences, similar wording and scoped assumptions supply no facts", () => {
  const cycle = runProofExploration(fixtureGraph(input([["AB", ["A"], "B"], ["BA", ["B"], "A"]], [])), { target: "B", budget: 100 });
  expect(cycle.forwardStatementIds).toEqual([]);
  expect(cycle.joins).toEqual([]);
  expect(cycle.status).toBe("complete");
  const data = input([["AB", ["A"], "B"]]);
  data.results = [];
  data.statements.forEach((s) => { s.paraphrase = "Identical wording"; });
  data.inferences[0].assumption_statement_ids = ["B"];
  const unchecked = runProofExploration(fixtureGraph(data), { target: "B", budget: 100 });
  expect(unchecked.forwardStatementIds).toEqual(["A"]);
  expect(unchecked.branches[0].remainingStatementIds).toEqual(["B"]);
  expect(unchecked.branches[0].resultIds).toEqual([]);
});

test("scope cannot promote open empirical premises and graph closure is untouched", () => {
  const graph = fixtureGraph(input([["AND", ["A", "EMPIRICAL"], "C"]]));
  const before = JSON.stringify(graph);
  const result = runProofExploration(graph, { target: "C", scope: ["EMPIRICAL"], budget: 100 });
  expect(result.establishedStatementIds).toEqual([]);
  expect(result.forwardStatementIds).toEqual([]);
  expect(result.branches[0].remainingStatementIds).toEqual(["A", "EMPIRICAL"]);
  expect(JSON.stringify(graph)).toBe(before);
});

test("budget and cancellation terminate deterministically between work items", () => {
  const graph = fixtureGraph(input([["AB", ["A"], "B"], ["BC", ["B"], "C"]]));
  const options = { target: "C", budget: 2 };
  const first = runProofExploration(graph, options);
  expect(first).toEqual(runProofExploration(graph, options));
  expect(first.status).toBe("budget-exhausted");
  expect(first.visits).toBe(2);
  const controller = new AbortController();
  const search = exploreProof(graph, { target: "C", budget: 100, signal: controller.signal });
  expect(search.next().done).toBe(false);
  controller.abort();
  let next = search.next();
  while (!next.done) { next = search.next(); }
  expect(next.value.status).toBe("cancelled");
  expect(next.value.visits).toBe(1);
});

test("lemma fallback is unformalized and unverified, with needs and exact provenance", async () => {
  const { suggestIntermediateLemma } = await import("./proof-exploration");
  const graph = fixtureGraph(input([["AND", ["A", "EMPIRICAL"], "C"]]));
  const search = runProofExploration(graph, { target: "C", budget: 100 });
  const candidate = suggestIntermediateLemma(search);
  expect(candidate?.status).toBe("unverified");
  expect(candidate?.formalization).toBe("unformalized");
  expect(candidate?.missingPremiseIds).toEqual(["EMPIRICAL"]);
  expect(candidate?.provenance.inferenceIds).toEqual(["I-AND"]);
  expect(candidate?.needs).toHaveLength(4);
  expect(suggestIntermediateLemma(runProofExploration(graph, { target: "C", budget: 0 }))).toBeNull();
  expect(suggestIntermediateLemma(runProofExploration(graph, { target: "A", budget: 100 }))).toBeNull();
});

test("discharged local assumptions are scoped subproof facts, never global forward seeds", () => {
  const data = input([["INTRO", ["B"], "C"]], []);
  data.results = [];
  data.inferences[0].assumption_statement_ids = ["B"];
  data.inferences[0].discharged_statement_ids = ["B"];
  const result = runProofExploration(fixtureGraph(data), { target: "C", budget: 100 });
  expect(result.forwardStatementIds).toEqual([]);
  expect(result.branches[0].remainingStatementIds).toEqual([]);
  expect(result.branches[0].scopedAssumptionIds).toEqual(["B"]);
  expect(result.branches[0].dischargedStatementIds).toEqual(["B"]);
  expect(result.joins).toEqual([]);
});
