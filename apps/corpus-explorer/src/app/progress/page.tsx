import Link from "next/link";
import { getCorpus, termsFor } from "@/lib/corpus";
import { getDossiers } from "@/lib/premise-dossier";
import { ProgressSearch } from "./search";

export default function ProgressPage() {
  const corpus = getCorpus();
  const dossiers = getDossiers();
  const entries = corpus.statements.map((statement) => {
    const dossier = dossiers[statement.id];
    const comparisonResults = corpus.results.filter((result) => result.research_comparisons?.some((cell) => cell.target_statement_id === statement.id));
    const arguments_ = corpus.arguments.filter((argument) => dossier.argument_ids.includes(argument.id) || comparisonResults.some((result) => result.argument_id === argument.id));
    const comparisonSenses = comparisonResults.flatMap((result) => (result.research_comparisons ?? []).filter((cell) => cell.target_statement_id === statement.id).map((cell) => cell.sense_definition_id));
    const terms = termsFor(corpus, [statement, ...arguments_]);
    return { id: statement.id, title: statement.paraphrase, established: dossier.established,
      search: [statement.id, statement.legacy_id, statement.label, statement.paraphrase, ...arguments_.flatMap((argument) => [argument.id, argument.legacy_id, argument.label]), ...corpus.definitions.filter((definition) => comparisonSenses.includes(definition.id)).flatMap((definition) => [definition.id, definition.label, definition.term]), ...terms.definitions.flatMap((definition) => [definition.id, definition.label, definition.term]), ...terms.disambiguations.map((entry) => entry.term)].join(" ") };
  });
  return <article><h1 className="font-serif text-4xl">Research progress</h1><p className="mt-3">Inspect a proposition’s senses, rivals, evidence and remaining gaps.</p><p className="mt-3"><Link className="link-quiet" href="/skeleton">Root connections</Link> · <Link className="link-quiet" href="/next">Next research priorities</Link></p><ProgressSearch entries={entries} /></article>;
}
