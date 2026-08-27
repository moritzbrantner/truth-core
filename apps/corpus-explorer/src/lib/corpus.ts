import { existsSync, readdirSync, readFileSync } from "node:fs";
import path from "node:path";

export type CorpusSource = {
  id: string;
  kind: "primary_text";
  author: string;
  work: string;
  citation_system: string;
  work_urn: string;
  reference_edition_urn?: string;
  catalog_url: string;
  notes: string;
};

export type CorpusSourceSnapshot = {
  source_id: string;
  edition_urn: string;
  language: string;
  repository: string;
  revision: string;
  path: string;
  git_blob_sha: string;
  source_url: string;
  license: string;
};

type CorpusPassageSlice = {
  id: string;
  locator: string;
  claim_locator_prefixes: string[];
  cts_path?: Array<{ subtype: string; n: string }>;
};

type CorpusPassageManifest = {
  snapshot: CorpusSourceSnapshot;
  passages: CorpusPassageSlice[];
  notes?: string;
};

export type CorpusPassage = CorpusSourceSnapshot &
  CorpusPassageSlice & {
    notes?: string;
  };

export type CorpusStatement = {
  id: string;
  paraphrase: string;
  lean_declaration?: string;
};

type RawCorpusClaim = {
  id: string;
  statement_id: string;
  source_id: string;
  locator: string;
  interpretation_group?: string;
  interpretation_of?: string;
  interpretation: string;
  status: "formalized";
};

export type CorpusClaim = RawCorpusClaim & {
  statement: CorpusStatement;
  passage: CorpusPassage;
  paraphrase: string;
  lean_declaration?: string;
};

export type CorpusInference = {
  id: string;
  input_statement_ids: string[];
  output_statement_id: string;
  rule: string;
  meaning: string;
  assumption_statement_ids: string[];
  discharged_statement_ids: string[];
};

export type CorpusArgument = {
  id: string;
  premise_statement_ids: string[];
  conclusion_statement_id: string;
  inference_ids: string[];
  meaning: string;
};

type RawCorpusResult = {
  id: string;
  argument_id: string;
  challenge_module: string;
  solution_module: string;
  theorem: string;
  comparator_config: string;
  status: "solution-present";
};

export type CorpusResult = RawCorpusResult & {
  argument: CorpusArgument;
  meaning: string;
};

export type CorpusRelation = {
  id: string;
  subject_kind: "source" | "statement" | "claim" | "inference" | "argument";
  subject_id: string;
  predicate: string;
  object_kind: "source" | "statement" | "claim" | "inference" | "argument";
  object_id: string;
  basis?: string;
};

export type CorpusCandidate = {
  id: string;
  source_id: string;
  locator: string;
  priority: number;
  goal: string;
  reason: string;
  status: "candidate";
};

export type ComparatorConfig = {
  permitted_axioms: string[];
  enable_nanoda: boolean;
};

export type ClaimListEntry = {
  id: string;
  sourceId: string;
  author: string;
  work: string;
  locator: string;
  paraphrase: string;
  status: CorpusClaim["status"];
  hasVerifiedArgument: boolean;
};

export type Corpus = {
  sources: CorpusSource[];
  passages: CorpusPassage[];
  statements: CorpusStatement[];
  claims: CorpusClaim[];
  inferences: CorpusInference[];
  arguments: CorpusArgument[];
  relations: CorpusRelation[];
  results: CorpusResult[];
  candidates: CorpusCandidate[];
};

const corpusDirectory = path.resolve(process.cwd(), "../..", "corpus");

function readRecords<Record>(directory: string): Record[] {
  if (!existsSync(directory)) {
    return [];
  }

  return readdirSync(directory)
    .filter((file) => file.endsWith(".json"))
    .sort()
    .map((file) => JSON.parse(readFileSync(path.join(directory, file), "utf8")));
}

function readPassages(): CorpusPassage[] {
  return readRecords<CorpusPassageManifest>(path.join(corpusDirectory, "passages")).flatMap((manifest) =>
    manifest.passages.map((passage) => ({
      ...manifest.snapshot,
      ...passage,
      notes: manifest.notes,
    })),
  );
}

function passageForRawClaim(passages: CorpusPassage[], claim: RawCorpusClaim) {
  const matches = passages.filter(
    (passage) =>
      passage.source_id === claim.source_id &&
      passage.claim_locator_prefixes.some((prefix) => claim.locator.startsWith(prefix)),
  );

  if (matches.length !== 1) {
    throw new Error(
      `Claim ${claim.id} must resolve to exactly one source passage; matched ${matches.length}`,
    );
  }

  return matches[0];
}

export function getCorpus(): Corpus {
  const sources = readRecords<CorpusSource>(path.join(corpusDirectory, "sources"));
  const passages = readPassages();
  const statements = readRecords<CorpusStatement>(path.join(corpusDirectory, "statements"));
  const rawClaims = readRecords<RawCorpusClaim>(path.join(corpusDirectory, "claims"));
  const inferences = readRecords<CorpusInference>(path.join(corpusDirectory, "inferences"));
  const arguments_ = readRecords<CorpusArgument>(path.join(corpusDirectory, "arguments"));
  const relations = readRecords<CorpusRelation>(path.join(corpusDirectory, "relations"));
  const rawResults = readRecords<RawCorpusResult>(path.join(corpusDirectory, "results"));
  const candidates = readRecords<CorpusCandidate>(path.join(corpusDirectory, "candidates"));

  const statementById = new Map(statements.map((statement) => [statement.id, statement]));
  const argumentById = new Map(arguments_.map((argument) => [argument.id, argument]));

  const claims = rawClaims.map((claim) => {
    const statement = statementById.get(claim.statement_id);
    if (!statement) {
      throw new Error(`Unknown statement ${claim.statement_id} for claim ${claim.id}`);
    }

    return {
      ...claim,
      statement,
      passage: passageForRawClaim(passages, claim),
      paraphrase: statement.paraphrase,
      lean_declaration: statement.lean_declaration,
    };
  });

  const results = rawResults.map((result) => {
    const argument = argumentById.get(result.argument_id);
    if (!argument) {
      throw new Error(`Unknown argument ${result.argument_id} for result ${result.id}`);
    }
    return { ...result, argument, meaning: argument.meaning };
  });

  return {
    sources,
    passages,
    statements,
    claims,
    inferences,
    arguments: arguments_,
    relations,
    results,
    candidates,
  };
}

export function findSource(corpus: Corpus, sourceId: string) {
  return corpus.sources.find((source) => source.id === sourceId);
}

export function findPassage(corpus: Corpus, passageId: string) {
  return corpus.passages.find((passage) => passage.id === passageId);
}

export function findStatement(corpus: Corpus, statementId: string) {
  return corpus.statements.find((statement) => statement.id === statementId);
}

export function findClaim(corpus: Corpus, claimId: string) {
  return corpus.claims.find((claim) => claim.id === claimId);
}

export function findInference(corpus: Corpus, inferenceId: string) {
  return corpus.inferences.find((inference) => inference.id === inferenceId);
}

export function findArgument(corpus: Corpus, argumentId: string) {
  return corpus.arguments.find((argument) => argument.id === argumentId);
}

export function findResult(corpus: Corpus, resultId: string) {
  return corpus.results.find((result) => result.id === resultId);
}

export function findCandidate(corpus: Corpus, candidateId: string) {
  return corpus.candidates.find((candidate) => candidate.id === candidateId);
}

export function passagesForSource(corpus: Corpus, sourceId: string) {
  return corpus.passages.filter((passage) => passage.source_id === sourceId);
}

export function claimsForStatement(corpus: Corpus, statementId: string) {
  return corpus.claims.filter((claim) => claim.statement_id === statementId);
}

export function argumentsUsingStatement(corpus: Corpus, statementId: string) {
  return corpus.arguments.filter((argument) => argument.premise_statement_ids.includes(statementId));
}

export function argumentsConcludingStatement(corpus: Corpus, statementId: string) {
  return corpus.arguments.filter((argument) => argument.conclusion_statement_id === statementId);
}

export function resultsForArgument(corpus: Corpus, argumentId: string) {
  return corpus.results.filter((result) => result.argument_id === argumentId);
}

export function resultsForClaim(corpus: Corpus, claimId: string) {
  const claim = findClaim(corpus, claimId);
  if (!claim) {
    return [];
  }
  const argumentIds = new Set(
    argumentsUsingStatement(corpus, claim.statement_id).map((argument) => argument.id),
  );
  return corpus.results.filter((result) => argumentIds.has(result.argument_id));
}

export function claimsForSource(corpus: Corpus, sourceId: string) {
  return corpus.claims.filter((claim) => claim.source_id === sourceId);
}

export function claimsForResult(corpus: Corpus, resultId: string) {
  const result = findResult(corpus, resultId);
  if (!result) {
    return [];
  }
  const premiseIds = new Set(result.argument.premise_statement_ids);
  return corpus.claims.filter((claim) => premiseIds.has(claim.statement_id));
}

export function statementsForArgument(corpus: Corpus, argumentId: string) {
  const argument = findArgument(corpus, argumentId);
  if (!argument) {
    return [];
  }
  const ids = [...argument.premise_statement_ids, argument.conclusion_statement_id];
  return ids.flatMap((id) => {
    const statement = findStatement(corpus, id);
    return statement ? [statement] : [];
  });
}

export function inferencesForArgument(corpus: Corpus, argumentId: string) {
  const argument = findArgument(corpus, argumentId);
  if (!argument) {
    return [];
  }
  return argument.inference_ids.flatMap((id) => {
    const inference = findInference(corpus, id);
    return inference ? [inference] : [];
  });
}

export function claimListEntries(corpus: Corpus): ClaimListEntry[] {
  return corpus.claims
    .flatMap((claim) => {
      const source = findSource(corpus, claim.source_id);
      if (!source) {
        return [];
      }
      return [
        {
          id: claim.id,
          sourceId: source.id,
          author: source.author,
          work: source.work,
          locator: claim.locator,
          paraphrase: claim.paraphrase,
          status: claim.status,
          hasVerifiedArgument: resultsForClaim(corpus, claim.id).length > 0,
        },
      ];
    })
    .sort(
      (left, right) =>
        left.author.localeCompare(right.author) ||
        left.work.localeCompare(right.work) ||
        left.locator.localeCompare(right.locator),
    );
}

export function alternativeClaims(corpus: Corpus, claim: CorpusClaim) {
  if (!claim.interpretation_group) {
    return [];
  }
  return corpus.claims.filter(
    (candidate) =>
      candidate.interpretation_group === claim.interpretation_group && candidate.id !== claim.id,
  );
}

export function comparatorForResult(result: CorpusResult): ComparatorConfig {
  return JSON.parse(
    readFileSync(path.resolve(corpusDirectory, "..", result.comparator_config), "utf8"),
  );
}
