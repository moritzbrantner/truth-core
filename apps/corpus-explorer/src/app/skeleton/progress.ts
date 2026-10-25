import type { Corpus } from "@/lib/corpus";
import type { ResearchObligation } from "@/lib/research-frontier";
import { resultKind, type FrontierReport } from "@/lib/site-state";

type ProgressCorpus = Pick<Corpus, "arguments" | "inferences" | "results" | "relations" | "statements">;

/** A presentation of existing records, never another closure or proof-search rule. */
export function skeletonProgress(
  corpus: ProgressCorpus,
  report: FrontierReport,
  research: ResearchObligation[],
) {
  const established = new Set(report.established_statements);
  const open = report.items
    .filter((item) => item.path_to_root !== null)
    .sort((a, b) => Number(a.depth !== "bare") - Number(b.depth !== "bare") || a.statement_id.localeCompare(b.statement_id));
  const openFor = (id: string) => open.filter(
    (item) => item.statement_id === id || item.transitive_dependent_statements.includes(id),
  );
  const routeIds = new Set(corpus.relations
    .filter((relation) => relation.predicate === "root_route" && relation.object_id === report.root)
    .map((relation) => relation.subject_id));
  const routes = corpus.arguments
    .filter((argument) => routeIds.has(argument.id))
    .sort((a, b) => a.id.localeCompare(b.id))
    .map((argument) => ({
      argument,
      results: corpus.results.filter((result) => result.argument_id === argument.id),
      connections: argument.inference_ids.flatMap((id) => {
        const inference = corpus.inferences.find((entry) => entry.id === id);
        if (!inference) {
          return [];
        }
        const results = corpus.results.filter((result) =>
          result.argument.conclusion_statement_id === inference.output_statement_id &&
          result.argument.inference_ids.includes(inference.id) &&
          // Other root arguments are alternative routes, not evidence consumed by this route.
          (inference.output_statement_id !== report.root || result.argument_id === argument.id),
        );
        const hasDerivation = results.some((result) => resultKind(report, result.id).kind === "derivation");
        let status: "discharged" | "connected" | "transcribed" | "recorded" = "recorded";
        if (established.has(inference.output_statement_id)) {
          status = "discharged";
        } else if (hasDerivation) {
          status = "connected";
        } else if (results.length) {
          status = "transcribed";
        }
        return [{ inference, results, status, open: openFor(inference.output_statement_id) }];
      }),
    }));
  const obligations = open.map((item) => ({
    item,
    // These are explicit statement-ID references in existing candidates, not inferred readings.
    candidates: research.filter((entry) => entry.kind === "exploration" && entry.statementIds.includes(item.statement_id)),
  }));
  return { root: report.root, discharged: established.has(report.root), routes, obligations };
}
