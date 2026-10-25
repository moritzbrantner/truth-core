import Link from "next/link";
import { notFound } from "next/navigation";

import { StatusMark } from "@/components/status-mark";
import { TermsSection } from "@/components/terms-section";
import {
  alternativeClaims,
  findClaim,
  findSource,
  getCorpus,
  isMediaPassage,
  isWebPassage,
  resultsForClaim,
} from "@/lib/corpus";

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
  const passage = claim.passage;
  const results = resultsForClaim(corpus, claim.id);
  const alternatives = alternativeClaims(corpus, claim);
  const sourcedDefinitions = corpus.definitions.filter((definition) => definition.claim_ids?.includes(claim.id));

  return (
    <article className="max-w-4xl">
      <Link className="link-quiet text-sm" href="/claims">
        ← All claims
      </Link>
      <div className="mt-10 flex flex-wrap items-center gap-3">
        <StatusMark>Source reading</StatusMark>
        <p className="font-mono text-xs text-[var(--muted)]">{claim.id}</p>
        <Link className="link-quiet text-xs" href={`/statements/${claim.statement_id}`}>
          Statement {claim.statement_id} →
        </Link>
      </div>
      <h1 className="mt-5 font-serif text-5xl leading-[0.98] tracking-[-0.05em] sm:text-6xl">
        {claim.paraphrase}
      </h1>

      {source ? (
        <p className="mt-7 text-lg leading-8 text-[var(--muted)]">
          <Link className="link-quiet" href={`/sources/${source.id}`}>
            {source.author}, <em>{source.work}</em>
          </Link>{" "}
          · {claim.locator}
        </p>
      ) : null}

      {isMediaPassage(passage) ? (
        <section className="record-section">
          <div className="flex flex-wrap items-center gap-3">
            <p className="eyebrow">Recorded-speech evidence</p>
            <StatusMark tone="accent">Pinned transcript span</StatusMark>
          </div>
          <p className="mt-4 text-lg leading-8 text-[var(--ink)]">
            This claim is bound to media span{" "}
            <span className="font-mono text-base">{passage.id}</span>. Only the span&apos;s
            timestamps and hash are stored; the transcript text is regenerated locally from
            youtube-corpus and rejected on a hash mismatch.
          </p>
          <dl className="mt-6 grid gap-4 text-sm sm:grid-cols-[11rem_minmax(0,1fr)]">
            <dt>Span</dt>
            <dd>{passage.locator}</dd>
            <dt>Video</dt>
            <dd>
              <a
                className="link-quiet break-all"
                href={`https://www.youtube.com/watch?v=${passage.youtube_id}&t=${Math.floor(passage.start_seconds)}`}
                rel="noreferrer"
                target="_blank"
              >
                Open the recording at the span ↗
              </a>
            </dd>
            {passage.speaker ? (
              <>
                <dt>Speaker</dt>
                <dd>
                  {passage.speaker}
                  {passage.speaker_attribution ? (
                    <span className="block text-[var(--muted)]">{passage.speaker_attribution}</span>
                  ) : null}
                </dd>
              </>
            ) : null}
            <dt>Transcript</dt>
            <dd className="font-mono break-all">
              {passage.transcript_source} ({passage.language}), {passage.segment_count} segments
            </dd>
            <dt>Producer</dt>
            <dd className="font-mono break-all">
              {passage.producer} {passage.producer_revision} · {passage.export_schema}
            </dd>
            <dt>Span hash</dt>
            <dd className="font-mono break-all">{passage.span_sha256}</dd>
            <dt>License</dt>
            <dd>{passage.license}</dd>
          </dl>
        </section>
      ) : isWebPassage(passage) ? (
        <section className="record-section">
          <div className="flex flex-wrap items-center gap-3">
            <p className="eyebrow">{passage.translation ? "Translation evidence" : "Web evidence"}</p>
            <StatusMark tone="accent">Pinned web snapshot</StatusMark>
          </div>
          <p className="mt-4 text-lg leading-8 text-[var(--ink)]">
            This claim is bound to passage <span className="font-mono text-base">{passage.id}</span>{" "}
            of a web page pinned by the hash of its bytes. No page text is stored; the selected
            range is re-extracted locally and rejected on any byte or text drift.
            {passage.translation
              ? " The page is a translation: the claim is read from it until a pinned original-language witness exists."
              : null}
          </p>
          <dl className="mt-6 grid gap-4 text-sm sm:grid-cols-[11rem_minmax(0,1fr)]">
            <dt>Passage</dt>
            <dd>{passage.locator}</dd>
            <dt>Page</dt>
            <dd>
              <a
                className="link-quiet break-all"
                href={passage.source_url}
                rel="noreferrer"
                target="_blank"
              >
                {passage.source_url} ↗
              </a>
            </dd>
            {passage.translation ? (
              <>
                <dt>Translation</dt>
                <dd>
                  {passage.translation.translator} ({passage.translation.year}),{" "}
                  {passage.translation.edition}
                </dd>
              </>
            ) : null}
            <dt>Retrieved</dt>
            <dd className="font-mono break-all">{passage.retrieved_at}</dd>
            <dt>Page hash</dt>
            <dd className="font-mono break-all">{passage.sha256}</dd>
            {passage.wayback_url ? (
              <>
                <dt>Archived copy</dt>
                <dd>
                  <a
                    className="link-quiet break-all"
                    href={passage.wayback_url}
                    rel="noreferrer"
                    target="_blank"
                  >
                    Wayback Machine capture ↗
                  </a>
                </dd>
              </>
            ) : null}
            <dt>Terms</dt>
            <dd>{passage.license}</dd>
          </dl>
        </section>
      ) : (
        <section className="record-section">
          <div className="flex flex-wrap items-center gap-3">
            <p className="eyebrow">Primary-source evidence</p>
            <StatusMark tone="accent">Pinned witness</StatusMark>
          </div>
          <p className="mt-4 text-lg leading-8 text-[var(--ink)]">
            This claim is bound to passage <span className="font-mono text-base">{passage.id}</span>{" "}
            in an immutable source snapshot. The snapshot is byte-verified separately from the
            scholarly interpretation below.
          </p>
          <dl className="mt-6 grid gap-4 text-sm sm:grid-cols-[11rem_minmax(0,1fr)]">
            <dt>Passage</dt>
            <dd>{passage.locator}</dd>
            <dt>Edition</dt>
            <dd className="font-mono break-all">{passage.edition_urn}</dd>
            <dt>Witness</dt>
            <dd>
              <a
                className="link-quiet break-all"
                href={passage.source_url}
                rel="noreferrer"
                target="_blank"
              >
                Open immutable source snapshot ↗
              </a>
            </dd>
            <dt>Revision</dt>
            <dd className="font-mono break-all">{passage.revision}</dd>
            <dt>Git blob</dt>
            <dd className="font-mono break-all">{passage.git_blob_sha}</dd>
            <dt>License</dt>
            <dd>{passage.license}</dd>
          </dl>
        </section>
      )}

      <section className="record-section">
        <p className="eyebrow">Interpretation</p>
        <p className="mt-4 text-lg leading-8 text-[var(--ink)]">{claim.interpretation}</p>
        <p className="mt-4 text-sm leading-6 text-[var(--muted)]">
          Source fidelity is a research/review judgment. A pinned witness proves what text was
          consulted; it does not make this interpretation mechanically true.
        </p>
      </section>

      <TermsSection corpus={corpus} records={[claim, claim.statement]} />

      {sourcedDefinitions.length ? (
        <section className="record-section">
          <p className="eyebrow">Definitions this reading sources</p>
          <ul className="mt-3 grid gap-2">
            {sourcedDefinitions.map((definition) => (
              <li key={definition.id}>
                <Link className="link-quiet font-serif text-lg" href={`/definitions/${definition.id}`}>
                  {definition.term}
                </Link>
              </li>
            ))}
          </ul>
        </section>
      ) : null}

      {alternatives.length ? (
        <section className="record-section">
          <p className="eyebrow">Alternative defensible readings</p>
          <div className="mt-4 divide-y divide-[var(--line)] border-y border-[var(--line)]">
            {alternatives.map((alternative) => (
              <Link
                className="block py-4 transition hover:text-[var(--accent)]"
                href={`/claims/${alternative.id}`}
                key={alternative.id}
              >
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
