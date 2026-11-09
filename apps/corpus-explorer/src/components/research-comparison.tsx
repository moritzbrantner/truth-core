import Link from "next/link";
import { certificateOutcome, comparisonOutcomes, senseCellOutcome } from "@/lib/research-progress";
import { getCorpus, nameOf, termsFor } from "@/lib/corpus";
import type { PremiseDossier } from "@/lib/premise-dossier";
import { getFrontierReport } from "@/lib/site-state";
import { getRegisteredConfigurationCases } from "@/lib/configuration-cases";
import { getVerifiedConfigurations } from "@/lib/verified-configurations";

/** Only explicit canonical evidence is displayed; sense proximity supplies no outcome. */
export function ResearchComparison({ dossier }: { dossier: PremiseDossier }) {
  const corpus = getCorpus();
  const report = getFrontierReport();
  const id = dossier.statement.id;
  const terms = termsFor(corpus, [{ definition_ids: dossier.definition_ids, disambiguation_ids: dossier.disambiguation_ids }]);
  const rivalIds = [...new Set(corpus.relations.filter((entry) => dossier.alternative_relation_ids.includes(entry.id) || dossier.objection_relation_ids.includes(entry.id)).map((entry) => entry.subject_id === id ? entry.object_id : entry.subject_id).filter((other) => corpus.statements.some((statement) => statement.id === other)))];
  const recordedCells = corpus.results.flatMap((result) => (result.research_comparisons ?? []).filter((cell) => cell.target_statement_id === id).map((cell) => ({ cell, result })));
  const cases = (getVerifiedConfigurations()?.cases ?? getRegisteredConfigurationCases()).filter((entry) => entry.seed_statement_id === id);
  const support = report.support_options.items.find((entry) => entry.statement_id === id);
  return <section id="research-comparison" className="record-section [overflow-wrap:anywhere]" aria-labelledby="comparison-heading">
    <h2 id="comparison-heading" className="font-serif text-2xl">Sense and rival comparison</h2>
    <p className="mt-3">{dossier.established ? "Established under corpus closure rules" : "Not established"}. Conditional support options do not establish their open premises.</p>
    <h3 className="mt-4 font-semibold">Verified conditional support options</h3>
    {support?.verified_alternative_bundles.length ? support.verified_alternative_bundles.map((bundle, index) => <div className="mt-3" key={index}><p>Premises: {bundle.premise_statement_ids.map(nameOf).join("; ") || "none"}</p>{bundle.result_ids.map((resultId) => <Link className="link-quiet mr-3" key={resultId} href={`/results/${resultId}`}>{nameOf(resultId)}</Link>)}</div>) : <p>No verified support bundle recorded in the frontier projection. Inspect arguments below for other recorded work.</p>}
    <h3 className="mt-4 font-semibold">Explicit certificate mappings</h3>
    {recordedCells.length ? recordedCells.map(({cell, result}, index) => <div className="mt-3" key={`${result.id}:${index}`}>
      <p><Link className="link-quiet" href={`/definitions/${cell.sense_definition_id}`}>{nameOf(cell.sense_definition_id)}</Link> × <Link className="link-quiet" href={`/statements/${cell.rival_statement_id}`}>{nameOf(cell.rival_statement_id)}</Link>: {certificateOutcome(cell.outcome, Boolean(report.transcription_results[result.id]))}</p>
      <p>Conditions: {cell.conditions}</p><p>Scope: {cell.scope}</p><p>Coverage: {cell.coverage} · Exclusivity: {cell.exclusivity}</p>
      {cell.witness ? <p>Witness: {cell.witness}</p> : null}{cell.gap ? <p>Gap: {cell.gap}</p> : null}
      <Link className="link-quiet" href={`/results/${result.id}`}>{nameOf(result.id)} · {result.theorem}</Link><p>{result.argument.meaning}</p><p>Next: {cell.next_step}</p>
    </div>) : <p>No explicit certificate mapping recorded. Nearby proofs and attempt outcomes supply no cell classification.</p>}
    <h3 className="mt-4 font-semibold">Explicitly linked senses</h3>
    <p>Scope: only the disambiguations linked to this dossier. Coverage and exclusivity for this target are unknown unless explicitly supplied by the evidence below. This list is not an exhaustive case split.</p>
    {!terms.disambiguations.length ? <p className="mt-2">Unknown / untested: no relevant sense mapping recorded.</p> : terms.disambiguations.map((term) => <div className="mt-3" key={term.id}><Link className="link-quiet" href={`/definitions#${term.id}`}>{term.term}</Link><p>{term.resolution}</p>{[term.coverage_statement_id, term.exclusivity_statement_id].map((statementId, index) => <p key={index}>{index ? "Exclusivity" : "Coverage"}: {statementId ? <Link className="link-quiet" href={`/statements/${statementId}`}>{nameOf(statementId)}</Link> : "unknown / not recorded"}</p>)}<table className="mt-3 w-full text-left text-sm"><thead><tr><th>Recorded sense</th><th>Rival</th><th>Case outcome</th></tr></thead><tbody>{term.sense_definition_ids.flatMap((sense) => (rivalIds.length ? rivalIds : [null]).map((rival) => <tr className="border-t" key={`${sense}:${rival}`}><td className="p-2"><Link className="link-quiet" href={`/definitions/${sense}`}>{nameOf(sense)}</Link></td><td className="p-2">{rival ? <Link className="link-quiet" href={`/dossiers/${rival}#research-comparison`}>{nameOf(rival)}</Link> : "Unknown: no rival recorded"}</td><td className="p-2">{recordedCells.some(({cell}) => cell.sense_definition_id === sense && cell.rival_statement_id === rival) ? "See explicit certificate mapping above; retain its conditions." : senseCellOutcome()} Select the same meaning, witness, domain and frame before comparing.</td></tr>))}</tbody></table></div>)}
    <h3 className="mt-4 font-semibold">Recorded rival exclusions</h3>
    {rivalIds.length ? rivalIds.map((rival) => <div className="mt-3" key={rival}><Link className="link-quiet" href={`/statements/${rival}`}>{nameOf(rival)}</Link>{report.refutations.filter((entry) => entry.statement_id === rival).map((entry) => <p key={entry.relation_id}>{entry.verified ? "Verified refutation under its listed premises" : "Verification not recorded"} · {entry.counted ? "counts for closure" : "does not count for closure"}. {corpus.results.filter((result) => result.argument_id === entry.argument_id).map((result) => <Link className="link-quiet mr-2" key={result.id} href={`/results/${result.id}`}>{nameOf(result.id)} · {result.theorem}</Link>)} Unestablished conditions: {(entry.unestablished_premise_statement_ids ?? entry.open_premise_statement_ids).map(nameOf).join("; ") || "none listed"}</p>)}<p>No exclusion here implies compatibility; scope remains that of each theorem.</p></div>) : <p>No rival linked. Coverage remains unknown.</p>}
    <h3 className="mt-4 font-semibold">Scoped assumption comparisons</h3>
    {cases.length ? cases.map((entry) => <div className="mt-3" key={entry.id}><Link className="link-quiet" href={`/configurations/${entry.id}`}>Inspect {nameOf(entry.id)}: outcomes and exact certificates</Link><p>{entry.scope}</p><p>Frame: {entry.semantics.frame} · Domain: {entry.semantics.domain} · Identity: {entry.semantics.identity}</p>{comparisonOutcomes(entry).map((cell) => <p key={cell.id}>{nameOf(cell.id)} · {cell.status} · assumptions: {cell.premises.map(nameOf).join("; ")}</p>)}</div>) : <p>Untested: no assumption comparison registered for this target. A model evaluation below concerns only its exact statement and assignment, not joint compatibility with a rival.</p>}
    <h3 className="mt-4 font-semibold">Remaining gap and next step</h3>
    {dossier.attempts.filter((attempt) => attempt.blocker).map((attempt) => <p className="mt-2" key={attempt.id}><Link className="link-quiet" href={`/attempts/${attempt.id}`}>{attempt.kind} · {attempt.outcome}</Link>: {attempt.blocker}</p>)}
    <p className="mt-2">Next: inspect the recorded attempt evidence and resolve a named open condition, or select an untested sense/rival cell and record its exact comparison assumptions. Attempt success alone supplies no proof status.</p>
    <Link className="link-quiet mt-3 inline-block" href="/progress">Find another argument, proposition or sense</Link>
  </section>;
}
