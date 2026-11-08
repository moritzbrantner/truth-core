import { expect, test } from "bun:test";

import { getCorpus } from "@/lib/corpus";
import { legacyUuid } from "@/lib/corpus-ids";
import { getFrontierReport } from "@/lib/site-state";
import { ASSEMBLY_RESULT_ID, buildGodWalkthrough, GOD_ROOT_ID } from "./walkthrough";

test("the guide projects the registered same-witness chain and open route, without new closure rules", () => {
  const corpus = getCorpus();
  const report = getFrontierReport(GOD_ROOT_ID);
  const guide = buildGodWalkthrough(corpus, report);

  expect(guide.stages.map((stage) => stage.result.id)).toEqual([
    legacyUuid("result", "DIRECT-ESSE-ROOT-PERFECTION"),
    legacyUuid("result", "PERFECT-ROOT-POSITIVE-INTELLECT-WILL"),
    ASSEMBLY_RESULT_ID,
  ]);
  expect(guide.stages[1].premises.some((premise) => premise.fromPreviousStep &&
    premise.statement.id === guide.stages[0].conclusion.id)).toBe(true);
  expect(guide.stages[2].premises.some((premise) => premise.fromPreviousStep &&
    premise.statement.id === guide.stages[1].conclusion.id)).toBe(true);
  expect(guide.stages[2].conclusion.id).toBe(GOD_ROOT_ID);

  expect(guide.rootRoutes).toEqual(report.routes.routes);
  expect(guide.route.premise_count).toBe(guide.stages[2].premises.length);
  expect(guide.route.cost).toBe(guide.route.open_premise_statement_ids.length);
  expect(guide.openLeaves.map((statement) => statement.id)).toEqual(guide.route.open_premise_statement_ids);
  expect(report.transcription_results[ASSEMBLY_RESULT_ID]?.kind).toBe("assembly");

  for (const stage of guide.stages) {
    expect(stage.premises.map((premise) => premise.statement.id)).toEqual(stage.result.argument.premise_statement_ids);
    for (const focus of stage.focus) {
      expect(stage.result.argument.premise_statement_ids).toContain(focus.statement.id);
    }
    for (const claim of stage.sourceClaims) {
      expect(stage.result.argument.premise_statement_ids).toContain(claim.statement_id);
    }
  }
}, 30000);

test("the guide refuses a frontier report for another conclusion", () => {
  const corpus = getCorpus();
  const unrelatedReport = { ...getFrontierReport(GOD_ROOT_ID), root: legacyUuid("statement", "STMT-CATHOLICISM-TRUE") };
  expect(() => buildGodWalkthrough(corpus, unrelatedReport)).toThrow(/Expected the frontier report/);
});
