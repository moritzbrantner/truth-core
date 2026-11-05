import Link from "next/link";
import { notFound } from "next/navigation";

import { findStatement, getCorpus } from "@/lib/corpus";
import { getAttempts } from "@/lib/premise-dossier";

export function generateStaticParams() {
  return Object.keys(getAttempts()).map((attemptId) => ({ attemptId }));
}

export default async function AttemptPage({ params }: { params: Promise<{ attemptId: string }> }) {
  const { attemptId } = await params;
  const attempt = getAttempts()[attemptId];
  if (!attempt) {
    notFound();
  }
  const corpus = getCorpus();
  const evidenceHref = (id: string) => {
    if (/^PR-[1-9][0-9]*$/.test(id)) {
      return `https://github.com/moritzbrantner/truth-core/pull/${id.slice(3)}`;
    }
    return corpus.results.some((entry) => entry.id === id) ? `/results/${id}` : `/claims/${id}`;
  };

  return (
    <article className="max-w-5xl [overflow-wrap:anywhere]">
      <h1 className="mt-8 font-serif text-4xl">Research attempt</h1>
      <p className="mt-3 font-mono text-xs break-all text-[var(--muted)]">{attempt.id}</p>
      <p className="mt-4 text-sm">{attempt.date} · {attempt.kind} · {attempt.outcome}</p>
      <section className="record-section" aria-labelledby="attempt-summary">
        <h2 id="attempt-summary" className="eyebrow">Findings and limits</h2>
        <p className="mt-3 whitespace-pre-wrap leading-7">{attempt.summary}</p>
        {attempt.blocker ? <p className="mt-3 text-sm whitespace-pre-wrap"><strong>Remaining blocker:</strong> {attempt.blocker}</p> : null}
      </section>
      <section className="record-section" aria-labelledby="attempt-evidence">
        <h2 id="attempt-evidence" className="eyebrow">Evidence</h2>
        {attempt.evidence.length ? <ul className="mt-3 flex flex-wrap gap-x-4 gap-y-2">{attempt.evidence.map((id) => <li key={id}>
          <Link className="link-quiet font-mono text-xs" href={evidenceHref(id)}>{id}</Link>
        </li>)}</ul> : <p className="mt-3 text-sm text-[var(--muted)]">No evidence reference recorded.</p>}
      </section>
      <section className="record-section" aria-labelledby="attempt-statements">
        <h2 id="attempt-statements" className="eyebrow">Related propositions</h2>
        <ul className="mt-3 grid gap-3">{attempt.statement_ids.map((id) => <li key={id}>
          <Link className="link-quiet font-mono text-xs break-all" href={`/dossiers/${id}#${attempt.id}`}>{id} · Dossier →</Link>
          <p className="mt-1 text-sm">{findStatement(corpus, id)?.paraphrase ?? "Statement record unavailable"}</p>
        </li>)}</ul>
      </section>
    </article>
  );
}
