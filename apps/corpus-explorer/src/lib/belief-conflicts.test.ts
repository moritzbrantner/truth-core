import { expect, test } from "bun:test";

import { activeCertifiedCores, reviewNewBelief, type CertifiedBeliefCore } from "./belief-conflicts";

const core = (key: string, statementIds: string[], profile = "S5"): CertifiedBeliefCore => ({
  key, statementIds, profile, caseId: "CASE", resultIds: ["RESULT-" + key],
});

test("a new belief yields all inclusion-minimal repair choices, not a fictitious forced rejection", () => {
  const cores = [core("one", ["P", "A", "B"]), core("two", ["P", "B", "C"])];
  const review = reviewNewBelief(new Set(["A", "B", "C"]), "P", cores);
  expect(review.cores).toHaveLength(2);
  expect(review.repairs).toEqual([["B"], ["A", "C"]]);
  expect(review.truncated).toBe(false);
  expect(activeCertifiedCores(new Set(["P", "A", "C"]), cores)).toEqual([]);
});

test("no existing beliefs need removal unless a complete certified core is activated", () => {
  const cores = [core("partial", ["P", "A", "B"]), core("unrelated", ["A", "C"]), core("different", ["P", "Z"])];
  expect(reviewNewBelief(new Set(["A"]), "P", cores).cores).toEqual([]);
  expect(reviewNewBelief(new Set(["A", "B"]), "P", cores).repairs).toEqual([["A"], ["B"]]);
});

test("a singleton core cannot be repaired by rejecting old beliefs, and incomplete enumeration is disclosed", () => {
  const singleton = reviewNewBelief(new Set(["A"]), "P", [core("single", ["P"])]);
  expect(singleton.cannotRepairByRejectingOldBeliefs).toBe(true);
  expect(singleton.repairs).toEqual([]);
  const limited = reviewNewBelief(new Set(["A", "B", "C"]), "P", [
    core("one", ["P", "A", "B", "C"]),
  ], 2);
  expect(limited.truncated).toBe(true);
  expect(limited.repairs).toEqual([["A"], ["B"]]);
});
