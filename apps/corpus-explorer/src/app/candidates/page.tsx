import Link from "next/link";

import { StatusMark } from "@/components/status-mark";
import { findSource, getCorpus } from "@/lib/corpus";

export default function CandidatesPage() {
  const corpus = getCorpus();
  const candidates = [...corpus.candidates].sort((left, right) => right.priority - left.priority);

  return (
    <section className="max-w-4xl">
      <p className="eyebrow">Open research</p>
      <h1 className="mt-4 font-serif text-5xl tracking-[-0.05em] sm:text-6xl">Research queue</h1>
      <p className="mt-6 max-w-3xl text-lg leading-8 text-[var(--muted)]">
        Candidates identify work that merits source research. They are not corpus findings or formalized claims.
      </p>
      <div className="mt-12 grid gap-4">
        {candidates.map((candidate) => {
          const source = findSource(corpus, candidate.source_id);
          return (
            <Link className="record-link" href={`/candidates/${candidate.id}`} key={candidate.id}>
              <StatusMark tone="muted">Research candidate</StatusMark>
              <h2 className="mt-4 font-serif text-3xl leading-tight tracking-[-0.03em]">{candidate.goal}</h2>
              {source ? <p className="mt-4 text-sm text-[var(--muted)]">{source.author}, {source.work} · {candidate.locator}</p> : null}
            </Link>
          );
        })}
      </div>
    </section>
  );
}
