import Link from "next/link";
import { notFound } from "next/navigation";

import { StatusMark } from "@/components/status-mark";
import { findCandidate, findSource, getCorpus } from "@/lib/corpus";

type CandidatePageProps = {
  params: Promise<{ candidateId: string }>;
};

export function generateStaticParams() {
  return getCorpus().candidates.map((candidate) => ({ candidateId: candidate.id }));
}

export default async function CandidatePage({ params }: CandidatePageProps) {
  const { candidateId } = await params;
  const corpus = getCorpus();
  const candidate = findCandidate(corpus, candidateId);

  if (!candidate) {
    notFound();
  }

  const source = findSource(corpus, candidate.source_id);

  return (
    <article className="max-w-4xl">
      <Link className="link-quiet text-sm" href="/candidates">
        ← Research queue
      </Link>
      <div className="mt-10">
        <StatusMark tone="muted">Research candidate</StatusMark>
      </div>
      <h1 className="mt-5 font-serif text-5xl leading-[0.98] tracking-[-0.05em] sm:text-6xl">{candidate.goal}</h1>
      {source ? (
        <p className="mt-7 text-lg leading-8 text-[var(--muted)]">
          <Link className="link-quiet" href={`/sources/${source.id}`}>
            {source.author}, <em>{source.work}</em>
          </Link>{" "}
          · {candidate.locator}
        </p>
      ) : null}

      <section className="record-section">
        <p className="eyebrow">Why this research is needed</p>
        <p className="mt-4 text-lg leading-8">{candidate.reason}</p>
      </section>

      <details className="record-section details-panel">
        <summary>Queue record</summary>
        <dl className="mt-5 grid gap-5 text-sm sm:grid-cols-[11rem_minmax(0,1fr)]">
          <dt>Priority</dt>
          <dd>{candidate.priority}</dd>
          <dt>Record ID</dt>
          <dd className="font-mono break-all">{candidate.id}</dd>
          <dt>Status</dt>
          <dd>Candidate</dd>
        </dl>
      </details>
    </article>
  );
}
