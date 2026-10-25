import { expect, test } from "bun:test";

import fixture from "../../../../../scripts/testdata/objective-truth-pilot.json";
import { fixtureGraph } from "@/lib/frontier-fixture";
import { getCorpus } from "@/lib/corpus";
import { getFrontierReport, statementState } from "@/lib/site-state";
import { getPilotScenarios, PILOT_GROUPS, pilotGraphHref } from "./pilot";

const corpus = getCorpus();
const report = getFrontierReport();

test("logical facts are established while interpretation bridges remain open", () => {
  for (const id of PILOT_GROUPS[0].statementIds) {
    expect(statementState(report, id)).toMatchObject({ kind: "closed", established: true });
  }
  for (const id of PILOT_GROUPS[1].statementIds) {
    expect(statementState(report, id).kind).toBe("open");
  }
  const ids = PILOT_GROUPS.flatMap((group) => group.statementIds);
  expect(new Set(ids).size).toBe(ids.length);
  expect(ids.every((id) => corpus.statements.some((statement) => statement.id === id))).toBe(true);
});

test("real reciprocal implications are not grounding without an independent result", () => {
  const scenarios = getPilotScenarios();
  expect(scenarios.map((scenario) => scenario.verifiedResults)).toEqual([0, 2, 3]);
  expect(scenarios.map((scenario) => scenario.established)).toEqual([
    [], [], ["STMT-NOT-EVERY-LEAN-PROPOSITION-FAILS", "STMT-SOME-LEAN-PROPOSITION-HOLDS"],
  ]);
});

test("global/local/epistemic readings and withheld assent do not become refuted", () => {
  const readings = PILOT_GROUPS[2].statementIds;
  for (const id of [...readings, "STMT-EXCLUDED-MIDDLE-WITHHELD-INTUITIONISM"]) {
    expect(report.established_statements).not.toContain(id);
  }
  expect(corpus.relations.filter((relation) => relation.predicate === "refutes" && readings.includes(relation.object_id))).toEqual([]);
});

test("pilot links select the exact goal and statement in the frontier graph", () => {
  const id = "STMT-PILOT-LOGICAL-SENTENCE-STABLE";
  const url = new URL(pilotGraphHref(id), "https://example.test");
  expect(url.pathname).toBe("/graph");
  expect(url.searchParams.get("scope")).toBe("goal");
  expect(url.searchParams.get("target")).toBe(id);
  expect(url.searchParams.get("node")).toBe(id);
  expect(url.searchParams.get("sel")).toBe(id);
});

test("frontend preserves the canonical reciprocal fixture's grounding distinction", () => {
  const arguments_ = corpus.arguments.filter((argument) => fixture.argument_ids.includes(argument.id));
  const inferenceIds = new Set(arguments_.flatMap((argument) => argument.inference_ids));
  for (const scenario of fixture.cases) {
    const graph = fixtureGraph({
      statements: corpus.statements.filter((statement) => fixture.statement_ids.includes(statement.id)),
      arguments: arguments_,
      inferences: corpus.inferences.filter((inference) => inferenceIds.has(inference.id)),
      results: corpus.results.filter((result) => scenario.result_ids.includes(result.id)),
      claims: [], sources: [], relations: [], transcriptionResultIds: [],
    });
    expect(graph.statements.filter((statement) => statement.established).map((statement) => statement.id).sort()).toEqual(scenario.expected_established);
    expect(graph.statements).toHaveLength(2);
  }
});
