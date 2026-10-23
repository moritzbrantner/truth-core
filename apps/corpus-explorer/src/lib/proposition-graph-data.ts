import { getCorpus, type Corpus } from "./corpus";
import { transcriptionFlags } from "./lean-transcription";
import { buildPropositionGraph, type PropositionGraph } from "./proposition-graph";

/** Build-time assembly of the /graph data from the corpus JSON and Lean sources. */
export function getPropositionGraph(corpus: Corpus = getCorpus()): PropositionGraph {
  return buildPropositionGraph({
    statements: corpus.statements,
    claims: corpus.claims.map((claim) => ({
      id: claim.id,
      statement_id: claim.statement_id,
      source_id: claim.source_id,
      locator: claim.locator,
      interpretation: claim.interpretation,
      interpretation_of: claim.interpretation_of,
      interpretation_group: claim.interpretation_group,
      passage_id: claim.passage.id,
    })),
    sources: corpus.sources,
    inferences: corpus.inferences,
    arguments: corpus.arguments,
    results: corpus.results,
    relations: corpus.relations,
    transcriptionResultIds: transcriptionFlags(corpus.results).map((flag) => flag.resultId),
  });
}
