import Link from "next/link";
import { notFound } from "next/navigation";

import { claimsForSource, findSource, getCorpus } from "@/lib/corpus";

type SourcePageProps = {
  params: Promise<{ sourceId: string }>;
};

export function generateStaticParams() {
  return getCorpus().sources.map((source) => ({ sourceId: source.id }));
}

export default async function SourcePage({ params }: SourcePageProps) {
  const { sourceId } = await params;
  const corpus = getCorpus();
  const source = findSource(corpus, sourceId);

  if (!source) {
    notFound();
  }

  const claims = claimsForSource(corpus, source.id).sort((left, right) => left.locator.localeCompare(right.locator));

  return (
    <article className="max-w-4xl">
      <Link className="link-quiet text-sm" href="/sources">
        ← All sources
      </Link>
      <p className="eyebrow mt-10">{source.citation_system} source record</p>
      <h1 className="mt-4 font-serif text-5xl tracking-[-0.05em] sm:text-6xl">
        {source.author}, <em>{source.work}</em>
      </h1>
      <p className="mt-6 max-w-3xl text-lg leading-8 text-[var(--muted)]">{source.notes}</p>

      <section className="record-section">
        <p className="eyebrow">Claims from this text</p>
        <div className="mt-4 divide-y divide-[var(--line)] border-y border-[var(--line)]">
          {claims.map((claim) => (
            <Link className="block py-5 transition hover:text-[var(--accent)]" href={`/claims/${claim.id}`} key={claim.id}>
              <p className="font-serif text-2xl leading-tight">{claim.paraphrase}</p>
              <p className="mt-2 text-sm text-[var(--muted)]">{claim.locator}</p>
            </Link>
          ))}
        </div>
      </section>

      <details className="record-section details-panel">
        <summary>Catalog and edition record</summary>
        <dl className="mt-5 grid gap-5 text-sm sm:grid-cols-[11rem_minmax(0,1fr)]">
          <dt>Catalog</dt>
          <dd>
            <a className="link-quiet break-all" href={source.catalog_url} rel="noreferrer" target="_blank">
              View stable catalog record ↗
            </a>
          </dd>
          <dt>Work identifier</dt>
          <dd className="font-mono break-all">{source.work_urn}</dd>
          {source.reference_edition_urn ? (
            <>
              <dt>Reference edition URN</dt>
              <dd className="font-mono break-all">{source.reference_edition_urn}</dd>
            </>
          ) : null}
        </dl>
      </details>
    </article>
  );
}
