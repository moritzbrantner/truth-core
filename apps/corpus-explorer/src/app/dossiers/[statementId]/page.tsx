import Link from "next/link";
import { notFound } from "next/navigation";

import { TermsSection } from "@/components/terms-section";
import { findStatement, getCorpus } from "@/lib/corpus";
import { getDossiers } from "@/lib/premise-dossier";

export function generateStaticParams() {
  return Object.keys(getDossiers()).map((statementId) => ({ statementId }));
}

export default async function DossierPage({ params }: { params: Promise<{ statementId: string }> }) {
  const { statementId } = await params;
  const dossier = getDossiers()[statementId];
  if (!dossier) {
    notFound();
  }
  const corpus = getCorpus();
  const statement = findStatement(corpus, statementId);
  if (!statement) {
    notFound();
  }
  const claims = corpus.claims.filter((entry) => dossier.claim_ids.includes(entry.id) || dossier.supporting_claim_ids.includes(entry.id));
  const arguments_ = corpus.arguments.filter((entry) => dossier.argument_ids.includes(entry.id));
  const relations = corpus.relations.filter((entry) => dossier.alternative_relation_ids.includes(entry.id) || dossier.objection_relation_ids.includes(entry.id));
  const evidenceHref = (id: string) => {
    if (/^PR-[1-9][0-9]*$/.test(id)) {
      return `https://github.com/moritzbrantner/truth-core/pull/${id.slice(3)}`;
    }
    return corpus.results.some((entry) => entry.id === id) ? `/results/${id}` : `/claims/${id}`;
  };
  const status = dossier.closure ?? (dossier.frontier ? `open · ${dossier.frontier.depth}` : "not on the frontier");
  return (
    <article className="max-w-5xl [overflow-wrap:anywhere]">
      <Link className="link-quiet text-sm" href={`/statements/${statementId}`}>← Statement and proof context</Link>
      <h1 className="mt-8 font-serif text-4xl">Premise dossier</h1>
      <p className="mt-3 font-mono text-xs break-all text-[var(--muted)]">{statement.id}</p>
      <p className="mt-4 text-xl leading-8">{statement.paraphrase}</p>
      <section className="record-section" aria-labelledby="dossier-status">
        <h2 id="dossier-status" className="eyebrow">Current status</h2>
        <p className="mt-3">{status} · {dossier.established ? "established" : "not established"}</p>
        <p className="mt-3 font-mono text-sm break-all">{statement.lean_declaration ?? "No Lean declaration recorded."}</p>
        <p className="mt-3 text-sm text-[var(--muted)]">Attempts record work and its outcome. They do not prove a statement or change frontier closure.</p>
      </section>
      <section className="record-section" aria-labelledby="dossier-sources">
        <h2 id="dossier-sources" className="eyebrow">Source readings</h2>
        {claims.length ? <ul className="mt-4 grid gap-4">{claims.map((claim) => <li key={claim.id}>
          <Link className="link-quiet font-mono text-xs" href={`/claims/${claim.id}`}>{claim.id}</Link>
          <p className="text-sm text-[var(--muted)]">{dossier.claim_ids.includes(claim.id) ? "States this proposition" : "Supports this proposition"} · {claim.source_id} · {claim.locator}{claim.witness === "bibliographic" ? " · bibliographic citation, not byte-verified" : ""}</p>
          <p className="mt-2 text-sm leading-6">{claim.interpretation}</p>
        </li>)}</ul> : <p className="mt-3">No source reading states or supports this proposition.</p>}
      </section>
      <TermsSection corpus={corpus} records={[{ definition_ids: dossier.definition_ids, disambiguation_ids: dossier.disambiguation_ids }]} />
      <section className="record-section" aria-labelledby="dossier-rivals">
        <h2 id="dossier-rivals" className="eyebrow">Alternatives and objections</h2>
        {relations.length ? <ul className="mt-4 grid gap-3">{relations.map((relation) => {
          const other = relation.subject_id === statementId ? relation.object_id : relation.subject_id;
          const otherStatement = findStatement(corpus, other);
          return <li key={relation.id}>
            <p className="text-sm text-[var(--muted)]">{relation.subject_id} → {relation.predicate.replaceAll("_", " ")} → {relation.object_id}</p>
            {relation.note || relation.basis ? <p className="mt-2 text-sm leading-6">{relation.note ?? relation.basis}</p> : null}
            {otherStatement ? <Link className="link-quiet" href={`/statements/${other}`}>{otherStatement.paraphrase}</Link> : <p>{other}</p>}
          </li>;
        })}</ul> : <p className="mt-3">No alternative or objection is linked.</p>}
      </section>
      <section className="record-section" aria-labelledby="dossier-proofs">
        <h2 id="dossier-proofs" className="eyebrow">Arguments and results</h2>
        {arguments_.length ? <ul className="mt-4 grid gap-4">{arguments_.map((argument) => {
          const results = corpus.results.filter((entry) => entry.argument_id === argument.id);
          let role = "Inference step";
          if (argument.conclusion_statement_id === statementId) { role = "Conclusion"; }
          else if (argument.premise_statement_ids.includes(statementId)) { role = "Premise"; }
          else if (argument.commitment_statement_ids?.includes(statementId)) { role = "Commitment"; }
          return <li key={argument.id}>
            <p className="font-mono text-xs break-all">{role} · {argument.id}</p>
            <p className="mt-2 text-sm leading-6">{argument.meaning}</p>
            {results.length ? results.map((result) => <p className="mt-2 text-sm" key={result.id}>
              <Link className="link-quiet font-mono text-xs" href={`/results/${result.id}`}>{result.id}</Link>
              {dossier.transcription_result_ids.includes(result.id) ? " · transcription; no independent closure" : " · see result and remaining premises"}
              <span className="mt-1 block font-mono text-xs break-all text-[var(--muted)]">{result.theorem}</span>
            </p>) : <p className="mt-2 text-sm text-[var(--muted)]">No result recorded.</p>}
          </li>;
        })}</ul> : <p className="mt-3">No argument uses or concludes this proposition.</p>}
      </section>
      <section className="record-section" aria-labelledby="dossier-instances">
        <h2 id="dossier-instances" className="eyebrow">Schema instances and countermodels</h2>
        <p className="mt-3 text-sm">Finite evaluations concern the registered vocabulary and assignments. They do not establish metaphysical possibility or close this premise. Schema registrations are not yet available.</p>
        <h3 className="mt-4 font-medium">Registered finite models</h3>
        {dossier.model_evaluations.length ? <ul className="mt-3 grid gap-4">{dossier.model_evaluations.map((model) => <li key={model.model_id}>
          <p className="font-mono text-xs">{model.model_id} · {model.value}</p>
          <p className="mt-1 text-sm">Vocabulary: {model.vocabulary}</p>
          <p className="mt-1 font-mono text-xs">{model.lean_declaration}</p>
          <details className="mt-2 text-sm"><summary>Statement application and certificate</summary>
            <p className="mt-2 font-mono text-xs">{statement.lean_declaration} {model.arguments.map((argument) => `(${argument})`).join(" ")}</p>
            <p className="mt-2 font-mono text-xs">{model.value === "violates" ? "Negation certificate: " : "Certificate: "}{model.theorem}</p>
          </details>
        </li>)}</ul> : <p className="mt-2 text-sm">No evaluation is registered. This gives no conclusion about consistency or derivability.</p>}
        <h3 className="mt-4 font-medium">Existing instantiation results</h3>
        {dossier.instantiation_result_ids.length ? <ul className="mt-2">{dossier.instantiation_result_ids.map((id) => <li key={id}><Link className="link-quiet font-mono text-xs" href={`/results/${id}`}>{id}</Link></li>)}</ul> : <p className="mt-2 text-sm">None recorded.</p>}
        <h3 className="mt-4 font-medium">Countermodel attempts</h3>
        {dossier.countermodel_attempt_ids.length ? <ul className="mt-2">{dossier.countermodel_attempt_ids.map((id) => <li key={id}><a className="link-quiet font-mono text-xs" href={`#${id}`}>{id}</a></li>)}</ul> : <p className="mt-2 text-sm">None recorded.</p>}
      </section>
      {dossier.configuration_cases?.length ? <section className="record-section" aria-labelledby="dossier-configurations">
        <h2 id="dossier-configurations" className="eyebrow">Configuration assumptions</h2>
        <ul className="mt-3 grid gap-3">{dossier.configuration_cases.map((entry) => <li key={entry.id}>
          <Link className="link-quiet font-mono text-xs" href={entry.href}>{entry.id}</Link>
          <p className="mt-1 text-sm">{entry.semantics_id} · {entry.verification}</p>
        </li>)}</ul>
      </section> : null}
      <section className="record-section" aria-labelledby="dossier-routes">
        <h2 id="dossier-routes" className="eyebrow">Route contribution</h2>
        <p className="mt-3 text-sm text-[var(--muted)]">A counted open leaf contributes one distinct member to that route’s current premise set. This is not the cost reduction that would follow from proving it.</p>
        <div className="mt-4 overflow-x-auto"><table className="w-full text-left text-sm">
          <caption className="sr-only">Open-leaf contribution to routes concluding {dossier.root}</caption>
          <thead><tr><th className="p-2">Route</th><th className="p-2">Open leaves</th><th className="p-2">Counted open leaf</th><th className="p-2">Direct premise</th></tr></thead>
          <tbody>{dossier.route_contributions.map((route) => <tr className="border-t border-[var(--line)]" key={route.argument_id}>
            <td className="p-2 font-mono text-xs break-all">{route.argument_id}</td><td className="p-2">{route.cost}</td><td className="p-2">{route.open_leaf ? "Yes" : "No"}</td><td className="p-2">{route.direct_premise ? "Yes" : "No"}</td>
          </tr>)}</tbody>
        </table></div>
      </section>
      <section className="record-section" aria-labelledby="dossier-attempts">
        <h2 id="dossier-attempts" className="eyebrow">Attempt log</h2>
        {dossier.attempts.length ? <ol className="mt-4 grid gap-5">{dossier.attempts.map((attempt) => <li id={attempt.id} key={attempt.id}>
          <p className="text-sm">{attempt.date} · {attempt.kind} · {attempt.outcome}</p>
          <p className="mt-1 font-mono text-xs break-all">{attempt.id}</p>
          <p className="mt-2 leading-7">{attempt.summary}</p>
          {attempt.blocker ? <p className="mt-2 text-sm"><strong>Remaining blocker:</strong> {attempt.blocker}</p> : null}
          <ul className="mt-2 flex flex-wrap gap-x-4 gap-y-2">{attempt.evidence.map((id) => <li key={id}><Link className="link-quiet font-mono text-xs" href={evidenceHref(id)}>{id}</Link></li>)}</ul>
          {!attempt.evidence.length ? <p className="mt-2 text-sm text-[var(--muted)]">No evidence reference recorded.</p> : null}
        </li>)}</ol> : <p className="mt-3">No attempt is recorded for this proposition.</p>}
      </section>
    </article>
  );
}
