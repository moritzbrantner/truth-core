import { describe, expect, test } from "bun:test";

import { claimListEntries, getCorpus, resultsForClaim } from "./corpus";

describe("corpus reader", () => {
  test("reads the present corpus and its claim-to-result relationships", () => {
    const corpus = getCorpus();

    expect(corpus.sources).toHaveLength(4);
    expect(corpus.claims).toHaveLength(7);
    expect(corpus.results).toHaveLength(2);
    expect(corpus.candidates).toHaveLength(1);
    expect(resultsForClaim(corpus, "PLATO-TIM-28A-CAUSE-A")).toHaveLength(1);
  });

  test("orders claim rows by author, work, and locator", () => {
    const entries = claimListEntries(getCorpus());

    expect(entries.map((entry) => entry.id)).toEqual([
      "ARIST-CAT-2A-PRIMARY-SUBSTANCE-A",
      "ARIST-MET-1003A-BEING-QUA-BEING-A",
      "ARIST-MET-1003A-BEING-QUA-BEING-B",
      "ARIST-PHYS-194B-FOUR-CAUSES-A",
      "PLATO-TIM-28A-CAUSE-A",
      "PLATO-TIM-28A-CAUSE-B",
      "PLATO-TIM-28BC-COSMOS-GENERATED",
    ]);
  });
});
