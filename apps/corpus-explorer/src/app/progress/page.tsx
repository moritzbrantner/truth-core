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
    return { id: statement.id, title: statement.paraphrase, established: dossier.established, hasComparison: comparisonResults.length > 0,
      search: [statement.id, statement.legacy_id, statement.label, statement.paraphrase, ...arguments_.flatMap((argument) => [argument.id, argument.legacy_id, argument.label]), ...corpus.definitions.filter((definition) => comparisonSenses.includes(definition.id)).flatMap((definition) => [definition.id, definition.label, definition.term]), ...terms.definitions.flatMap((definition) => [definition.id, definition.label, definition.term]), ...terms.disambiguations.flatMap((entry) => [entry.term, ...(entry.senses ?? []).map((sense) => sense.label)])].join(" ") };
  });
  // The search shows at most 100 matches. A sense label matches every proposition that links its
  // disambiguation, so propositions with a recorded sense/rival comparison come first (stable
  // order otherwise); a broad sense search must not hide the canonical comparisons behind the cap.
  entries.sort((left, right) => Number(right.hasComparison) - Number(left.hasComparison));
  return <article><h1 className="font-serif text-4xl">Research progress</h1><p className="mt-3">Inspect a proposition’s senses, rivals, evidence and remaining gaps.</p><p className="mt-3"><Link className="link-quiet" href="/skeleton">Root connections</Link> · <Link className="link-quiet" href="/next">Next research priorities</Link></p><ProgressSearch entries={entries} /></article>;
}
