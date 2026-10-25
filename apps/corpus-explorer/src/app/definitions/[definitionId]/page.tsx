import Link from "next/link";
import { notFound } from "next/navigation";

import { StatementLink } from "@/components/statement-link";
import { disambiguationsForDefinition, findClaim, findDefinition, findSource, getCorpus, resultsForArgument, usesOfTerm } from "@/lib/corpus";
import { leanIndex } from "@/lib/lean-source";
import { getFrontierReport, sourceUrl } from "@/lib/site-state";

type DefinitionPageProps = {
  params: Promise<{ definitionId: string }>;
};

export function generateStaticParams() {
  return getCorpus().definitions.map((definition) => ({ definitionId: definition.id }));
}

export default async function DefinitionPage({ params }: DefinitionPageProps) {
  const { definitionId } = await params;
  const corpus = getCorpus();
  const definition = findDefinition(corpus, definitionId);
  if (!definition) {
    notFound();
  }
  const report = getFrontierReport();
  const lean = definition.lean_declaration ? leanIndex().get(definition.lean_declaration) : undefined;
  const disambiguations = disambiguationsForDefinition(corpus, definition.id);
  const uses = usesOfTerm(corpus, "definition_ids", definition.id);

  return (
    <article className="max-w-5xl">
      <Link className="link-quiet text-sm" href="/definitions">
        ← Definitions and disambiguations
      </Link>
      <div className="mt-10 flex flex-wrap items-center gap-3">
        <span className="eyebrow">{definition.basis === "sourced" ? "Sourced definition" : "Stipulative definition"}</span>
        <p className="font-mono text-xs break-all text-[var(--muted)]">{definition.id}</p>
      </div>
      <h1 className="mt-5 font-serif text-4xl leading-[1.02] tracking-[-0.04em] sm:text-5xl">{definition.term}</h1>
      <p className="mt-6 text-lg leading-8">{definition.definition}</p>
      {definition.note ? <p className="mt-4 text-sm leading-6 text-[var(--muted)]">{definition.note}</p> : null}

      <section className="record-section">
        <p className="eyebrow">Source</p>
        {definition.claim_ids?.length ? (
          <div className="mt-4 divide-y divide-[var(--line)] border-y border-[var(--line)]">
            {definition.claim_ids.map((id) => {
              const claim = findClaim(corpus, id);
              const source = claim ? findSource(corpus, claim.source_id) : undefined;
              return (
                <Link className="block py-4 transition hover:text-[var(--accent)]" href={`/claims/${id}`} key={id}>
                  <span className="mt-1 block font-serif text-lg">
                    {source ? `${source.author}, ${source.work}` : claim?.source_id} · {claim?.locator}
                  </span>
                  <span className="mt-1 block text-sm leading-6 text-[var(--muted)]">{claim?.interpretation}</span>
                  <span className="mt-1 block font-mono text-xs text-[var(--muted)]">{id}</span>
                </Link>
              );
            })}
          </div>
        ) : (
          <p className="mt-3 text-sm text-[var(--muted)]">Stipulated; the note above says why and what would source it.</p>
        )}
      </section>

      {disambiguations.length ? (
        <section className="record-section">
          <p className="eyebrow">One sense of an ambiguous term</p>
          {disambiguations.map((disambiguation) => (
            <div className="mt-4" key={disambiguation.id}>
              <Link className="font-serif text-lg hover:text-[var(--accent)]" href={`/definitions#${disambiguation.id}`}>
                {disambiguation.term}
              </Link>
              <p className="mt-2 text-sm leading-6">{disambiguation.resolution}</p>
              <p className="mt-2 text-xs text-[var(--muted)]">
                Other senses:{" "}
                {disambiguation.sense_definition_ids
                  .filter((id) => id !== definition.id)
                  .map((id, index) => (
                    <span key={id}>
                      {index ? " · " : ""}
                      <Link className="link-quiet" href={`/definitions/${id}`}>
                        {findDefinition(corpus, id)?.term ?? id}
                      </Link>
                    </span>
                  ))}
              </p>
            </div>
          ))}
        </section>
      ) : null}

      <section className="record-section">
        <p className="eyebrow">Used by</p>
        {uses.statements.length || uses.arguments.length || uses.claims.length ? (
          <>
            <ul className="premise-list mt-3">
              {uses.statements.map((statement) => (
                <StatementLink corpus={corpus} id={statement.id} key={statement.id} report={report} />
              ))}
            </ul>
            <ul className="mt-4 grid gap-2 text-sm">
              {uses.arguments.map((argument) => {
                const results = resultsForArgument(corpus, argument.id);
                return (
                  <li key={argument.id}>
                    <span className="eyebrow">argument</span>{" "}
                    {results.length ? (
                      <Link className="link-quiet font-mono text-xs" href={`/results/${results[0].id}`}>
                        {argument.id}
                      </Link>
                    ) : (
                      <span className="font-mono text-xs">{argument.id}</span>
                    )}
                  </li>
                );
              })}
              {uses.claims.map((claim) => (
                <li key={claim.id}>
                  <span className="eyebrow">claim</span>{" "}
                  <Link className="link-quiet font-mono text-xs" href={`/claims/${claim.id}`}>
                    {claim.id}
                  </Link>
                </li>
              ))}
            </ul>
          </>
        ) : (
          <p className="mt-3 text-sm text-[var(--muted)]">Linked only as a sense of a disambiguation.</p>
        )}
      </section>

      <section className="record-section">
        <p className="eyebrow">Lean declaration</p>
        {definition.lean_declaration ? (
          <>
            <p className="mt-3 font-mono text-sm break-all">{definition.lean_declaration}</p>
            {lean ? (
              <>
                <pre className="lean-snippet">{lean.snippet}</pre>
                <a className="link-quiet mt-2 inline-block text-sm" href={sourceUrl(lean.file, lean.line)} rel="noreferrer" target="_blank">
                  {lean.file}:{lean.line} ↗
                </a>
              </>
            ) : null}
          </>
        ) : (
          <p className="mt-3 text-sm text-[var(--muted)]">No Lean declaration is recorded for this sense.</p>
        )}
      </section>
    </article>
  );
}
