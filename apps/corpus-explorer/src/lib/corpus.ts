import { existsSync, readdirSync, readFileSync } from "node:fs";
import path from "node:path";

export type CorpusSource = {
  id: string;
  kind: "primary_text" | "media_recording";
  author: string;
  work: string;
  citation_system: string;
  work_urn: string;
  edition_urns?: string[];
  reference_edition_urn?: string;
  catalog_url: string;
  youtube_id?: string;
  channel?: string;
  upload_date?: string;
  notes: string;
};

export type CorpusSourceSnapshot = {
  kind?: "text_witness";
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
  tei_xml_id?: string;
};

/** A timed transcript span pinned by hash to a youtube-corpus export; no text is stored. */
export type CorpusMediaSnapshot = {
  kind: "media_span";
  source_id: string;
  youtube_id: string;
  transcript_source: "caption_manual" | "caption_auto" | "asr";
  language: string;
  producer: string;
  producer_revision: string;
  export_schema: string;
  source_url: string;
  license: string;
};

type CorpusMediaSpanSlice = CorpusPassageSlice & {
  start_seconds: number;
  end_seconds: number;
  segment_count: number;
  span_sha256: string;
  speaker?: string;
  speaker_attribution?: string;
};

/** A web page pinned by the SHA-256 of its response bytes; no page text is stored. */
export type CorpusWebSnapshot = {
  kind: "web_snapshot";
  source_id: string;
  source_url: string;
  retrieved_at: string;
  sha256: string;
  encoding: string;
  language: string;
  license: string;
  translation?: { translator: string; year: number | string; edition: string };
  wayback_url?: string;
  wayback_sha256?: string;
};

type CorpusWebSnapshotSlice = CorpusPassageSlice & {
  text_sha256: string;
  incipit?: string;
} & (
  | { html_selector: Record<string, unknown>; pdf_pages?: never }
  | { pdf_pages: { first: number; last: number }; html_selector?: never }
);

type CorpusPassageManifest =
  | { snapshot: CorpusSourceSnapshot; passages: CorpusPassageSlice[]; notes?: string }
  | { snapshot: CorpusMediaSnapshot; passages: CorpusMediaSpanSlice[]; notes?: string }
  | { snapshot: CorpusWebSnapshot; passages: CorpusWebSnapshotSlice[]; notes?: string }
  | {
      snapshot: Partial<CorpusBibliographicPassage> & { kind: "bibliographic_span" };
      passages: Array<Partial<CorpusBibliographicPassage> & CorpusPassageSlice>;
      notes?: string;
    };

/**
 * A copyrighted edition cited by page or section, with no pinned bytes (#378).
 * Bibliographic fields may sit on the snapshot or on each passage.
 */
export type CorpusBibliographicPassage = CorpusPassageSlice & {
  kind: "bibliographic_span";
  source_id: string;
  author: string;
  title: string;
  year: number;
  language: string;
  why_bibliographic: string;
  publisher?: string;
  journal?: string;
  edition?: string;
  isbn?: string;
  doi?: string;
  pages?: string;
  section?: string;
  quotation?: string;
  translation?: { translator: string; year: number | string; edition: string };
  notes?: string;
};

export type CorpusTextPassage = CorpusSourceSnapshot &
  CorpusPassageSlice & {
    notes?: string;
  };

export type CorpusMediaPassage = CorpusMediaSnapshot &
  CorpusMediaSpanSlice & {
    notes?: string;
  };

export type CorpusWebPassage = CorpusWebSnapshot &
  CorpusWebSnapshotSlice & {
    notes?: string;
  };

export type CorpusPassage =
  | CorpusTextPassage
  | CorpusMediaPassage
  | CorpusWebPassage
  | CorpusBibliographicPassage;

export function isBibliographicPassage(passage: CorpusPassage): passage is CorpusBibliographicPassage {
  return passage.kind === "bibliographic_span";
}

export function isMediaPassage(passage: CorpusPassage): passage is CorpusMediaPassage {
  return passage.kind === "media_span";
}

export function isWebPassage(passage: CorpusPassage): passage is CorpusWebPassage {
  return passage.kind === "web_snapshot";
}

export type CorpusStatement = {
  id: string;
  paraphrase: string;
  lean_declaration?: string;
  /** Optional premise-program marking (#156): sourced justification for self-evidence. */
  self_evident?: { justification_ids: string[] };
} & TermLinks;

/** Links from a statement, claim or argument to the senses of the terms it uses (#204). */
export type TermLinks = {
  definition_ids?: string[];
  disambiguation_ids?: string[];
};

/** One sense of a term: sourced from claims, or explicitly stipulative with a note. */
export type CorpusDefinition = {
  id: string;
  term: string;
  definition: string;
  basis: "sourced" | "stipulative";
  claim_ids?: string[];
  lean_declaration?: string;
  note?: string;
};

/** Two or more senses of one term, and which sense each use takes. */
export type CorpusDisambiguation = {
  id: string;
  term: string;
  sense_definition_ids: string[];
  resolution: string;
};

type RawCorpusClaim = TermLinks & {
  id: string;
  statement_id: string;
  source_id: string;
  locator: string;
  interpretation_group?: string;
  interpretation_of?: string;
  interpretation: string;
  /** Present on claims read from a translated web snapshot. */
  basis?: "translation";
  /** Present on claims cited from a bibliographic span: not byte-verified (#378). */
  witness?: "bibliographic";
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

export type CorpusArgument = TermLinks & {
  id: string;
  premise_statement_ids: string[];
  /** Statements a consistency argument shows jointly satisfiable (it may then have no premises). */
  commitment_statement_ids?: string[];
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
  /** Declared transcription kind (invariant 16, #391); closes nothing by rule (a). */
  transcription?: "opaque_atoms" | "single_application" | "assembly" | "instantiation";
  description?: string;
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
  note?: string;
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
  theorem_names?: string[];
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
  definitions: CorpusDefinition[];
  disambiguations: CorpusDisambiguation[];
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
  return readRecords<CorpusPassageManifest>(path.join(corpusDirectory, "passages")).flatMap(
    (manifest) =>
      manifest.passages.map(
        (passage) =>
          ({
            ...manifest.snapshot,
            ...passage,
            notes: manifest.notes,
          }) as CorpusPassage,
      ),
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
  const definitions = readRecords<CorpusDefinition>(path.join(corpusDirectory, "definitions"));
  const disambiguations = readRecords<CorpusDisambiguation>(path.join(corpusDirectory, "disambiguations"));

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
    definitions,
    disambiguations,
  };
}

export function findDefinition(corpus: Corpus, definitionId: string) {
  return corpus.definitions.find((definition) => definition.id === definitionId);
}

/** The disambiguations that list this definition as one of their senses. */
export function disambiguationsForDefinition(corpus: Corpus, definitionId: string) {
  return corpus.disambiguations.filter((disambiguation) => disambiguation.sense_definition_ids.includes(definitionId));
}

export type Terms = { definitions: CorpusDefinition[]; disambiguations: CorpusDisambiguation[] };

/**
 * The senses the records use and the ambiguities they must be read against:
 * the linked definitions, the linked disambiguations, and every disambiguation
 * that has a linked definition as one of its senses. Deduplicated, in order.
 */
export function termsFor(corpus: Corpus, records: TermLinks[]): Terms {
  const definitionIds = [...new Set(records.flatMap((record) => record.definition_ids ?? []))];
  const disambiguationIds = new Set(records.flatMap((record) => record.disambiguation_ids ?? []));
  for (const definitionId of definitionIds) {
    for (const disambiguation of disambiguationsForDefinition(corpus, definitionId)) {
      disambiguationIds.add(disambiguation.id);
    }
  }
  return {
    definitions: definitionIds.flatMap((id) => findDefinition(corpus, id) ?? []),
    disambiguations: corpus.disambiguations.filter((disambiguation) => disambiguationIds.has(disambiguation.id)),
  };
}

/** Statements, claims and arguments that link a definition or disambiguation. */
export function usesOfTerm(corpus: Corpus, field: keyof TermLinks, id: string) {
  const links = (record: TermLinks) => record[field]?.includes(id) ?? false;
  return {
    statements: corpus.statements.filter(links),
    claims: corpus.claims.filter(links),
    arguments: corpus.arguments.filter(links),
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
  return corpus.arguments.filter(
    (argument) =>
      argument.premise_statement_ids.includes(statementId) ||
      (argument.commitment_statement_ids ?? []).includes(statementId),
  );
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
  const premiseIds = new Set([
    ...result.argument.premise_statement_ids,
    ...(result.argument.commitment_statement_ids ?? []),
  ]);
  return corpus.claims.filter((claim) => premiseIds.has(claim.statement_id));
}

export function statementsForArgument(corpus: Corpus, argumentId: string) {
  const argument = findArgument(corpus, argumentId);
  if (!argument) {
    return [];
  }
  const ids = [
    ...argument.premise_statement_ids,
    ...(argument.commitment_statement_ids ?? []),
    argument.conclusion_statement_id,
  ];
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
