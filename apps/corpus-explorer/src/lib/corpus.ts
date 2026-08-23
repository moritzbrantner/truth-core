import { readdirSync, readFileSync } from "node:fs";
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

export type CorpusClaim = {
  id: string;
  source_id: string;
  locator: string;
  interpretation_group?: string;
  interpretation_of?: string;
  interpretation: string;
  paraphrase: string;
  lean_declaration: string;
  status: "formalized";
};

export type CorpusResult = {
  id: string;
  claim_ids: string[];
  challenge_module: string;
  solution_module: string;
  theorem: string;
  comparator_config: string;
  status: "solution-present";
  meaning: string;
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
  claims: CorpusClaim[];
  results: CorpusResult[];
  candidates: CorpusCandidate[];
};

const corpusDirectory = path.resolve(process.cwd(), "../..", "corpus");

function readRecords<Record>(directory: string): Record[] {
  return readdirSync(directory)
    .filter((file) => file.endsWith(".json"))
    .sort()
    .map((file) => JSON.parse(readFileSync(path.join(directory, file), "utf8")));
}

export function getCorpus(): Corpus {
  return {
    sources: readRecords<CorpusSource>(path.join(corpusDirectory, "sources")),
    claims: readRecords<CorpusClaim>(path.join(corpusDirectory, "claims")),
    results: readRecords<CorpusResult>(path.join(corpusDirectory, "results")),
    candidates: readRecords<CorpusCandidate>(path.join(corpusDirectory, "candidates")),
  };
}

export function findSource(corpus: Corpus, sourceId: string) {
  return corpus.sources.find((source) => source.id === sourceId);
}

export function findClaim(corpus: Corpus, claimId: string) {
  return corpus.claims.find((claim) => claim.id === claimId);
}

export function findResult(corpus: Corpus, resultId: string) {
  return corpus.results.find((result) => result.id === resultId);
}

export function findCandidate(corpus: Corpus, candidateId: string) {
  return corpus.candidates.find((candidate) => candidate.id === candidateId);
}

export function resultsForClaim(corpus: Corpus, claimId: string) {
  return corpus.results.filter((result) => result.claim_ids.includes(claimId));
}

export function claimsForSource(corpus: Corpus, sourceId: string) {
  return corpus.claims.filter((claim) => claim.source_id === sourceId);
}

export function claimsForResult(corpus: Corpus, resultId: string) {
  const result = findResult(corpus, resultId);
  if (!result) {
    return [];
  }

  return result.claim_ids.flatMap((claimId) => {
    const claim = findClaim(corpus, claimId);
    return claim ? [claim] : [];
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
