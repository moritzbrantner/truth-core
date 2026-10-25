import { expect, test } from "bun:test";

import { getCorpus } from "@/lib/corpus";
import { getPropositionGraph } from "@/lib/proposition-graph-data";
import { researchFrontier } from "@/lib/research-frontier";
import { getFrontierReport } from "@/lib/site-state";

import { skeletonProgress } from "./progress";

const corpus = getCorpus();
const report = getFrontierReport();
const research = researchFrontier(corpus, getPropositionGraph(corpus), report);
const progress = skeletonProgress(corpus, report, research);

test("the actual designated route retains exactly the authoritative open obligations", () => {
  expect(progress.routes.map(({ argument }) => argument.id)).toEqual([
    "CATHOLICISM-FROM-EFFICIENT-REGRESS-WITH-CLASSICAL-ATTRIBUTES",
  ]);
  expect(progress.obligations.map(({ item }) => item.statement_id).sort()).toEqual(
    report.items.filter((item) => item.path_to_root).map((item) => item.statement_id).sort(),
  );
  expect(progress.obligations.filter(({ item }) => item.depth === "bare").length).toBe(report.items.filter((item) => item.path_to_root && item.depth === "bare").length);
  expect(progress.discharged).toBe(false);
  expect(progress.routes[0].argument.premise_statement_ids).toEqual(corpus.arguments.find((argument) => argument.id === progress.routes[0].argument.id)?.premise_statement_ids);
});

test("checked connections remain conditional while established EM is discharged", () => {
  const connections = progress.routes[0].connections;
  const witness = connections.find(({ inference }) => inference.output_statement_id === "STMT-UNIQUE-GOD-WITH-CLASSICAL-ATTRIBUTES-EXISTS");
  expect(witness?.status).toBe("connected");
  expect(witness?.results.map((result) => result.id)).toEqual(["CATHOLICISM-STAGES-ONE-TWO-SAME-WITNESS"]);
  expect(connections.find(({ inference }) => inference.output_statement_id === "STMT-FIRST-UNMOVED-MOVER-EXISTS-OR-NOT")).toMatchObject({ status: "discharged", open: [] });
  expect(connections.find(({ inference }) => inference.output_statement_id === report.root)?.results.map((result) => result.id)).toEqual([
    "CATHOLICISM-FROM-EFFICIENT-REGRESS-WITH-CLASSICAL-ATTRIBUTES",
  ]);
  expect(progress.obligations.filter(({ item }) => item.depth === "sourced").length).toBe(report.items.filter((item) => item.path_to_root && item.depth === "sourced").length);
});

test("short proof advisory flags do not change a derivation into a transcription", () => {
  const first = progress.routes[0].connections[0];
  const flagged = skeletonProgress(corpus, {
    ...report,
    transcription_flags: [...report.transcription_flags, {
      result_id: first.results[0].id,
      argument_id: first.results[0].argument_id,
      proof_steps: 2,
      single_application_of: null,
      goal_consequent_premises: [],
    }],
  }, research);
  expect(flagged.routes[0].connections[0].status).toBe("connected");
});

test("recorded topology alone never advertises an independently checked connection", () => {
  const output = progress.routes[0].connections[0].inference.output_statement_id;
  const unbound = skeletonProgress({
    ...corpus,
    results: corpus.results.filter((result) => result.argument.conclusion_statement_id !== output),
  }, report, research);
  expect(unbound.routes[0].connections[0]).toMatchObject({ status: "recorded", results: [] });
});

test("only explicit candidate statement links are presented as a next recorded gap", () => {
  const bridge = progress.obligations.find(({ item }) => item.statement_id === "STMT-BRIDGE-CHRISTS-CHURCH-FOUNDED-BY-GOD");
  expect(bridge?.candidates.some((candidate) => candidate.recordIds.includes("CHRISTS-CHURCH-DIVINE-FOUNDING-BRIDGE"))).toBe(true);
  for (const { item, candidates } of progress.obligations) {
    expect(candidates.every((candidate) => candidate.kind === "exploration" && candidate.statementIds.includes(item.statement_id))).toBe(true);
  }
  const withoutCandidates = skeletonProgress(corpus, report, []);
  expect(withoutCandidates.obligations.every(({ candidates }) => candidates.length === 0)).toBe(true);
});

test("a missing designated route is explicit rather than choosing another root proof", () => {
  const unrouted = skeletonProgress({
    ...corpus,
    relations: corpus.relations.filter((relation) => relation.predicate !== "root_route"),
  }, report, research);
  expect(unrouted.routes).toEqual([]);
});
