import { describe, expect, test } from "bun:test";

import {
  claimListEntries,
  claimsForResult,
  findArgument,
  findClaim,
  findStatement,
  getCorpus,
  resultsForClaim,
} from "./corpus";

describe("corpus reader", () => {
  test("reads the independent statement and argument model", () => {
    const corpus = getCorpus();

    expect(corpus.sources).toHaveLength(4);
    expect(corpus.statements).toHaveLength(11);
    expect(corpus.claims).toHaveLength(9);
    expect(corpus.inferences).toHaveLength(2);
    expect(corpus.arguments).toHaveLength(2);
    expect(corpus.relations).toHaveLength(0);
    expect(corpus.results).toHaveLength(2);
    expect(corpus.candidates).toHaveLength(8);
    expect(resultsForClaim(corpus, "PLATO-TIM-28A-CAUSE-A")).toHaveLength(1);
  });

  test("keeps source claims separate from statement identity", () => {
    const corpus = getCorpus();
    const claim = findClaim(corpus, "PLATO-TIM-28A-CAUSE-A");
    const statement = findStatement(corpus, "STMT-CAUSE-PRINCIPLE-BROAD");
    const argument = findArgument(corpus, "PLATO-TIM-28A-28C-COSMOS-CAUSE-A");

    expect(claim?.statement_id).toBe(statement?.id);
    expect(argument?.premise_statement_ids).toContain(statement?.id);
    expect(argument?.premise_statement_ids).not.toContain(claim?.id);
    expect(claimsForResult(corpus, "PLATO-TIM-28A-28C-COSMOS-CAUSE-A")).toHaveLength(2);
  });

  test("allows a derived conclusion statement with no source claim", () => {
    const corpus = getCorpus();
    const argument = findArgument(corpus, "PLATO-TIM-28A-28C-COSMOS-CAUSE-A");

    expect(argument?.conclusion_statement_id).toBe("STMT-COSMOS-HAS-CAUSE");
    expect(corpus.claims.some((claim) => claim.statement_id === argument?.conclusion_statement_id)).toBe(false);
  });

  test("orders claim rows by author, work, and locator", () => {
    const entries = claimListEntries(getCorpus());

    expect(entries.map((entry) => entry.id)).toEqual([
      "ARIST-CAT-2A-PRIMARY-SUBSTANCE-A",
      "ARIST-MET-1003A-BEING-QUA-BEING-A",
      "ARIST-MET-1003A-BEING-QUA-BEING-B",
      "ARIST-PHYS-194B-FOUR-CAUSES-A",
      "ARIST-PHYS-201A-CHANGE-A",
      "ARIST-PHYS-201A-CHANGE-B",
      "PLATO-TIM-28A-CAUSE-A",
      "PLATO-TIM-28A-CAUSE-B",
      "PLATO-TIM-28BC-COSMOS-GENERATED",
    ]);
  });
});
