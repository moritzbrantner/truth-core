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
import { legacyUuid } from "./corpus-ids";

const statementId = (id: string) => legacyUuid("statement", id);
const definitionId = (id: string) => legacyUuid("definition", id);
const disambiguationId = (id: string) => legacyUuid("disambiguation", id);
const claimId = legacyUuid("claim", "PLATO-TIM-28A-CAUSE-A");
const argumentId = legacyUuid("argument", "PLATO-TIM-28A-28C-COSMOS-CAUSE-A");
const resultId = legacyUuid("result", "PLATO-TIM-28A-28C-COSMOS-CAUSE-A");

describe("definitions and disambiguations (#204)", () => {
  test("a statement's terms include the disambiguations of the senses it uses", () => {
    const corpus = getCorpus();
    const statement = findStatement(corpus, statementId("STMT-MAXIME-ENS-IS-GOD"));
    const terms = termsFor(corpus, statement ? [statement] : []);

    expect(terms.definitions.map((definition) => definition.id)).toContain(definitionId("DEF-MAXIME-ENS"));
    expect(terms.disambiguations.map((disambiguation) => disambiguation.id)).toEqual(
      expect.arrayContaining([disambiguationId("DISAMB-GOD"), disambiguationId("DISAMB-MAXIME-ENS")]),
    );
  });

  test("every linked definition and every sense resolves", () => {
    const corpus = getCorpus();
    const ids = new Set(corpus.definitions.map((definition) => definition.id));
    const linked = [...corpus.statements, ...corpus.claims, ...corpus.arguments].flatMap((record) => record.definition_ids ?? []);

    expect(linked.every((id) => ids.has(id))).toBe(true);
    expect(corpus.disambiguations.flatMap((entry) => entry.sense_definition_ids).every((id) => ids.has(id))).toBe(true);
    expect(usesOfTerm(corpus, "definition_ids", definitionId("DEF-MAXIME-ENS")).statements.length).toBeGreaterThan(0);
  });
});

describe("corpus reader", () => {
  test("reuses a production build snapshot but reloads outside production", () => {
    const originalMode = process.env.NODE_ENV;
    try {
      process.env.NODE_ENV = "production";
      const first = getCorpus();
      expect(getCorpus()).toBe(first);

      process.env.NODE_ENV = "development";
      const development = getCorpus();
      expect(development).not.toBe(first);
      expect(getCorpus()).not.toBe(development);

      process.env.NODE_ENV = "production";
      expect(getCorpus()).not.toBe(first);
    } finally {
      if (originalMode === undefined) {
        delete process.env.NODE_ENV;
      } else {
        process.env.NODE_ENV = originalMode;
      }
    }
  });

  test("reads the independent statement and argument model", () => {
    const corpus = getCorpus();

    expect(corpus.sources.some((source) => source.id === legacyUuid("source", "ARIST-PHYS"))).toBe(true);
    expect(corpus.statements.some((statement) => statement.id === statementId("STMT-CAUSE-PRINCIPLE-BROAD"))).toBe(true);
    expect(corpus.claims.some((claim) => claim.id === claimId)).toBe(true);
    expect(corpus.inferences.some((inference) => inference.id === legacyUuid("inference", "INF-PLATO-TIM-COSMOS-CAUSE-A"))).toBe(true);
    expect(corpus.arguments.some((argument) => argument.id === argumentId)).toBe(true);
    expect(corpus.results.some((result) => result.id === resultId)).toBe(true);
    expect(corpus.candidates.every((candidate) => candidate.status === "candidate")).toBe(true);
    // Membership, not a count: a later argument reusing the statement adds a result (#520).
    expect(resultsForClaim(corpus, claimId).map((result) => result.id)).toContain(resultId);
  });

  test("keeps source claims separate from statement identity", () => {
    const corpus = getCorpus();
    const claim = findClaim(corpus, claimId);
    const statement = findStatement(corpus, statementId("STMT-CAUSE-PRINCIPLE-BROAD"));
    const argument = findArgument(corpus, argumentId);

    expect(claim?.statement_id).toBe(statement?.id);
    expect(argument?.premise_statement_ids).toContain(statement?.id);
    expect(argument?.premise_statement_ids).not.toContain(claim?.id);
    const premiseClaims = claimsForResult(corpus, resultId);
    expect(premiseClaims.map((entry) => entry.id)).toContain(claimId);
    expect(premiseClaims.every((entry) => argument?.premise_statement_ids.includes(entry.statement_id))).toBe(true);
  });

  test("allows a derived conclusion statement with no source claim", () => {
    const corpus = getCorpus();
    const argument = findArgument(corpus, argumentId);

    expect(argument?.conclusion_statement_id).toBe(statementId("STMT-COSMOS-HAS-CAUSE"));
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
