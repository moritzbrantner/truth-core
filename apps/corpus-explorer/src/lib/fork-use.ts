import type { Corpus, CorpusResult } from "./corpus";

/** Exact declared case-split applications and their input/result bindings.
 * No semantics or verification status is inferred from prose or identifiers. */
export function forkUses(corpus: Pick<Corpus, "inferences" | "results">, result: CorpusResult) {
  return corpus.inferences
    .filter((step) => result.argument.inference_ids.includes(step.id) && step.rule === "disjunction_elimination")
    .map((step) => ({
      step,
      evidence: corpus.results.filter((producer) =>
        producer.id !== result.id && step.input_statement_ids.includes(producer.argument.conclusion_statement_id)),
    }))
    .filter((use) => use.evidence.length > 0)
    .sort((a, b) => a.step.id.localeCompare(b.step.id));
}
