import { Suspense } from "react";

import { ClaimExplorer } from "@/components/claim-explorer";
import { claimListEntries, getCorpus } from "@/lib/corpus";

export default function ClaimsPage() {
  const corpus = getCorpus();

  return (
    <>
      <section className="grid gap-8 lg:grid-cols-[minmax(0,1fr)_17rem] lg:items-end">
        <div>
          <p className="eyebrow">Source readings</p>
          <h1 className="mt-4 max-w-3xl font-serif text-5xl leading-[0.95] tracking-[-0.055em] sm:text-6xl">
            Philosophical findings, held to their sources.
          </h1>
          <p className="mt-6 max-w-2xl text-lg leading-8 text-[var(--muted)]">
            Truth Core records atomic readings of philosophical texts, their precise locators, and the arguments that can be mechanically verified from them.
          </p>
        </div>
        <dl className="grid grid-cols-2 gap-x-6 gap-y-5 border-l border-[var(--line)] pl-5 sm:grid-cols-4 lg:grid-cols-2">
          <div>
            <dt className="eyebrow">Sources</dt>
            <dd className="mt-1 font-serif text-4xl">{corpus.sources.length}</dd>
          </div>
          <div>
            <dt className="eyebrow">Claims</dt>
            <dd className="mt-1 font-serif text-4xl">{corpus.claims.length}</dd>
          </div>
          <div>
            <dt className="eyebrow">Arguments</dt>
            <dd className="mt-1 font-serif text-4xl">{corpus.results.length}</dd>
          </div>
          <div>
            <dt className="eyebrow">Candidates</dt>
            <dd className="mt-1 font-serif text-4xl">{corpus.candidates.length}</dd>
          </div>
        </dl>
      </section>

      <aside className="mt-12 border-l-2 border-[var(--accent)] bg-[var(--callout)] px-5 py-5 text-sm leading-6 text-[var(--muted)]">
        <strong className="font-semibold text-[var(--ink)]">A necessary distinction.</strong> A mechanically verified argument establishes a formal consequence of its advertised claims. It does not by itself establish that a source meant those claims.
      </aside>

      <Suspense fallback={<p className="mt-12 text-[var(--muted)]">Loading the claim index…</p>}>
        <ClaimExplorer claims={claimListEntries(corpus)} sources={corpus.sources} />
      </Suspense>
    </>
  );
}
