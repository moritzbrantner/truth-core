import { readFileSync } from "node:fs";
import path from "node:path";

import { getCorpus, type Corpus } from "./corpus";
import { areaOfNamespace, laneOfNamespace, parseAreas } from "./graph-areas";
import { getFrontierReport } from "./site-state";
import { buildPropositionGraph, type PropositionGraph } from "./proposition-graph";

let cachedAreas: string[] | undefined;

/** `AREAS` of scripts/root_imports.py, the single list of import areas. */
export function getImportAreas() {
  cachedAreas ??= parseAreas(readFileSync(path.resolve(process.cwd(), "../../scripts/root_imports.py"), "utf8"));
  return cachedAreas;
}

/** Build-time assembly of the /graph data from the corpus JSON and Lean sources. */
export function getPropositionGraph(corpus: Corpus = getCorpus()): PropositionGraph {
  const report = getFrontierReport();
  const graph = buildPropositionGraph({
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
  }, report);
  const areas = getImportAreas();
  return {
    ...graph,
    statements: graph.statements.map((statement) => ({
      ...statement,
      area: areaOfNamespace(statement.namespace, areas),
      lane: laneOfNamespace(statement.namespace),
    })),
  };
}
