import { describe, expect, test } from "bun:test";

import {
  claimListEntries,
  claimsForResult,
  findArgument,
  findClaim,
  findStatement,
  getCorpus,
  resultsForClaim,
  termsFor,
  usesOfTerm,
} from "./corpus";

describe("definitions and disambiguations (#204)", () => {
  test("a statement's terms include the disambiguations of the senses it uses", () => {
    const corpus = getCorpus();
    const statement = findStatement(corpus, "STMT-MAXIME-ENS-IS-GOD");
    const terms = termsFor(corpus, statement ? [statement] : []);

    expect(terms.definitions.map((definition) => definition.id)).toContain("DEF-MAXIME-ENS");
    expect(terms.disambiguations.map((disambiguation) => disambiguation.id)).toEqual(
      expect.arrayContaining(["DISAMB-GOD", "DISAMB-MAXIME-ENS"]),
    );
  });

  test("every linked definition and every sense resolves", () => {
    const corpus = getCorpus();
    const ids = new Set(corpus.definitions.map((definition) => definition.id));
    const linked = [...corpus.statements, ...corpus.claims, ...corpus.arguments].flatMap((record) => record.definition_ids ?? []);

    expect(linked.every((id) => ids.has(id))).toBe(true);
    expect(corpus.disambiguations.flatMap((entry) => entry.sense_definition_ids).every((id) => ids.has(id))).toBe(true);
    expect(usesOfTerm(corpus, "definition_ids", "DEF-MAXIME-ENS").statements.length).toBeGreaterThan(0);
  });
});

describe("corpus reader", () => {
  test("reads the independent statement and argument model", () => {
    const corpus = getCorpus();

    expect(corpus.sources.some((source) => source.id === "ARIST-PHYS")).toBe(true);
    expect(corpus.statements.some((statement) => statement.id === "STMT-CAUSE-PRINCIPLE-BROAD")).toBe(true);
    expect(corpus.claims.some((claim) => claim.id === "PLATO-TIM-28A-CAUSE-A")).toBe(true);
    expect(corpus.inferences.some((inference) => inference.id === "INF-PLATO-TIM-COSMOS-CAUSE-A")).toBe(true);
    expect(corpus.arguments.some((argument) => argument.id === "PLATO-TIM-28A-28C-COSMOS-CAUSE-A")).toBe(true);
    expect(corpus.results.some((result) => result.id === "PLATO-TIM-28A-28C-COSMOS-CAUSE-A")).toBe(true);
    expect(corpus.candidates.every((candidate) => candidate.status === "candidate")).toBe(true);
    // Membership, not a count: a later argument reusing the statement adds a result (#520).
    expect(resultsForClaim(corpus, "PLATO-TIM-28A-CAUSE-A").map((result) => result.id)).toContain("PLATO-TIM-28A-28C-COSMOS-CAUSE-A");
  });

  test("keeps source claims separate from statement identity", () => {
    const corpus = getCorpus();
    const claim = findClaim(corpus, "PLATO-TIM-28A-CAUSE-A");
    const statement = findStatement(corpus, "STMT-CAUSE-PRINCIPLE-BROAD");
    const argument = findArgument(corpus, "PLATO-TIM-28A-28C-COSMOS-CAUSE-A");

    expect(claim?.statement_id).toBe(statement?.id);
    expect(argument?.premise_statement_ids).toContain(statement?.id);
    expect(argument?.premise_statement_ids).not.toContain(claim?.id);
    const premiseClaims = claimsForResult(corpus, "PLATO-TIM-28A-28C-COSMOS-CAUSE-A");
    expect(premiseClaims.map((entry) => entry.id)).toContain("PLATO-TIM-28A-CAUSE-A");
    expect(premiseClaims.every((entry) => argument?.premise_statement_ids.includes(entry.statement_id))).toBe(true);
  });

  test("allows a derived conclusion statement with no source claim", () => {
    const corpus = getCorpus();
    const argument = findArgument(corpus, "PLATO-TIM-28A-28C-COSMOS-CAUSE-A");

    expect(argument?.conclusion_statement_id).toBe("STMT-COSMOS-HAS-CAUSE");
    expect(corpus.claims.some((claim) => claim.statement_id === argument?.conclusion_statement_id)).toBe(false);
  });

  test("orders claim rows by author, work, and locator", () => {
    const entries = claimListEntries(getCorpus());
    const expected = [...entries].sort((left, right) =>
      left.author.localeCompare(right.author) ||
      left.work.localeCompare(right.work) ||
      left.locator.localeCompare(right.locator),
    );

    expect(entries).toEqual(expected);
  });
});
