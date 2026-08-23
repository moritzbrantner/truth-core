import Link from "next/link";
import { notFound } from "next/navigation";

import { StatusMark } from "@/components/status-mark";
import { alternativeClaims, findClaim, findSource, getCorpus, resultsForClaim } from "@/lib/corpus";

type ClaimPageProps = {
  params: Promise<{ claimId: string }>;
};

export function generateStaticParams() {
  return getCorpus().claims.map((claim) => ({ claimId: claim.id }));
}

export default async function ClaimPage({ params }: ClaimPageProps) {
  const { claimId } = await params;
  const corpus = getCorpus();
  const claim = findClaim(corpus, claimId);

  if (!claim) {
    notFound();
  }

  const source = findSource(corpus, claim.source_id);
  const results = resultsForClaim(corpus, claim.id);
  const alternatives = alternativeClaims(corpus, claim);

  return (
    <article className="max-w-4xl">
      <Link className="link-quiet text-sm" href="/">
        ← All claims
      </Link>
      <div className="mt-10 flex flex-wrap items-center gap-3">
        <StatusMark>Source-derived claim</StatusMark>
        <p className="font-mono text-xs text-[var(--muted)]">{claim.id}</p>
      </div>
      <h1 className="mt-5 font-serif text-5xl leading-[0.98] tracking-[-0.05em] sm:text-6xl">{claim.paraphrase}</h1>

      {source ? (
        <p className="mt-7 text-lg leading-8 text-[var(--muted)]">
          <Link className="link-quiet" href={`/sources/${source.id}`}>
            {source.author}, <em>{source.work}</em>
          </Link>{" "}
          · {claim.locator}
        </p>
      ) : null}

      <section className="record-section">
        <p className="eyebrow">Interpretation</p>
        <p className="mt-4 text-lg leading-8 text-[var(--ink)]">{claim.interpretation}</p>
      </section>

      {alternatives.length ? (
        <section className="record-section">
          <p className="eyebrow">Alternative defensible readings</p>
          <div className="mt-4 divide-y divide-[var(--line)] border-y border-[var(--line)]">
            {alternatives.map((alternative) => (
              <Link className="block py-4 transition hover:text-[var(--accent)]" href={`/claims/${alternative.id}`} key={alternative.id}>
                <span className="font-serif text-xl">{alternative.paraphrase}</span>
                <span className="ml-3 text-sm text-[var(--muted)]">{alternative.id}</span>
              </Link>
            ))}
          </div>
        </section>
      ) : null}

      {results.length ? (
        <section className="record-section">
          <p className="eyebrow">Mechanically verified arguments</p>
          <div className="mt-4 grid gap-4">
            {results.map((result) => (
              <Link className="record-link" href={`/results/${result.id}`} key={result.id}>
                <StatusMark tone="accent">Mechanically verified argument</StatusMark>
                <p className="mt-3 font-serif text-2xl leading-tight">{result.meaning}</p>
                <p className="mt-3 font-mono text-xs text-[var(--muted)]">{result.id}</p>
              </Link>
            ))}
          </div>
        </section>
      ) : null}

      <details className="record-section details-panel">
        <summary>Formal record</summary>
        <dl className="mt-5 grid gap-5 text-sm sm:grid-cols-[11rem_minmax(0,1fr)]">
          <dt>Lean declaration</dt>
          <dd className="font-mono break-all text-[var(--ink)]">{claim.lean_declaration}</dd>
          <dt>Record status</dt>
          <dd>Formalized</dd>
          {claim.interpretation_group ? (
            <>
              <dt>Interpretation group</dt>
              <dd className="font-mono break-all">{claim.interpretation_group}</dd>
            </>
          ) : null}
        </dl>
      </details>
    </article>
  );
}
