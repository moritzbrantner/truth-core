import { expect, test } from "bun:test";
import { getCorpus } from "./corpus";
import { forkUses } from "./fork-use";

test("fork use follows exact inference inputs and producing result, not prose", () => {
  const corpus = getCorpus();
  const result = corpus.results.find((entry) => entry.id === "RECIPROCAL-EVENT-RESPECT-CONSTRAINT")!;
  const uses = forkUses(corpus, result);
  expect(uses.map((use) => use.step.id)).toEqual(["INF-TEMPORAL-RECIPROCAL-FORK-USE"]);
  expect(uses[0].evidence.map((entry) => entry.id)).toEqual(["TEMPORAL-DIRECTION-FRAMEWORK"]);
  expect(uses[0].evidence[0].argument.premise_statement_ids).toEqual([]);
  expect(uses[0].step.output_statement_id).toBe(result.argument.conclusion_statement_id);
  const unrelated = structuredClone(result);
  unrelated.argument.inference_ids = [];
  unrelated.meaning = "Fork applied here: TEMPORAL-DIRECTION-FRAMEWORK";
  expect(forkUses(corpus, unrelated)).toEqual([]);
  const noRule = { ...corpus, inferences: corpus.inferences.map((step) => ({ ...step, rule: "exploratory" })) };
  expect(forkUses(noRule, result)).toEqual([]);
});
