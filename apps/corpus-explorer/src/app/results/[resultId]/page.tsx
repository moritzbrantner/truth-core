import Link from "next/link";
import { notFound } from "next/navigation";

import { ArgumentFlow } from "@/components/argument-flow";
import { StatusMark } from "@/components/status-mark";
import { claimsForResult, comparatorForResult, findResult, getCorpus } from "@/lib/corpus";

type ResultPageProps = {
  params: Promise<{ resultId: string }>;
};

export function generateStaticParams() {
  return getCorpus().results.map((result) => ({ resultId: result.id }));
}

export default async function ResultPage({ params }: ResultPageProps) {
  const { resultId } = await params;
  const corpus = getCorpus();
  const result = findResult(corpus, resultId);

  if (!result) {
    notFound();
  }

  const claims = claimsForResult(corpus, result.id);
  const comparator = comparatorForResult(result);
  const projectionCorpus = {
    statements: corpus.statements,
    inferences: corpus.inferences,
    arguments: corpus.arguments,
    verified_argument_ids: corpus.results.map((entry) => entry.argument_id),
  };

  return (
    <article className="max-w-6xl">
      <Link className="link-quiet text-sm" href="/results">
        ← All verified arguments
      </Link>
      <div className="mt-10">
        <StatusMark tone="accent">Mechanically verified argument</StatusMark>
      </div>
      <h1 className="mt-5 max-w-4xl font-serif text-5xl leading-[0.98] tracking-[-0.05em] sm:text-6xl">{result.meaning}</h1>
      <p className="mt-6 font-mono text-sm text-[var(--muted)]">{result.id}</p>

      <aside className="mt-10 max-w-4xl border-l-2 border-[var(--accent)] bg-[var(--callout)] px-5 py-5 text-sm leading-6 text-[var(--muted)]">
        This result verifies formal consequence from the advertised claims. It does not verify the historical or philosophical truth of those claims.
      </aside>

      <section className="record-section">
        <p className="eyebrow">Argument composition</p>
        <h2 className="mt-3 font-serif text-3xl tracking-[-0.03em]">Proof projection</h2>
        <p className="mt-3 max-w-3xl text-sm leading-6 text-[var(--muted)]">
          Each argument is a reusable block. Expand a block to inspect its premises and inference steps; collapse it to compose larger proofs without turning the canonical corpus into a DAG.
        </p>
        <div className="mt-6">
          <ArgumentFlow corpus={projectionCorpus} rootArgumentId={result.argument_id} />
        </div>
      </section>

      <section className="record-section max-w-4xl">
        <p className="eyebrow">Advertised premises</p>
        <div className="mt-4 divide-y divide-[var(--line)] border-y border-[var(--line)]">
          {claims.map((claim) => (
            <Link className="block py-5 transition hover:text-[var(--accent)]" href={`/claims/${claim.id}`} key={claim.id}>
              <p className="font-serif text-2xl leading-tight">{claim.paraphrase}</p>
              <p className="mt-2 font-mono text-xs text-[var(--muted)]">{claim.id}</p>
            </Link>
          ))}
        </div>
      </section>

      <details className="record-section details-panel max-w-4xl">
        <summary>Comparator record</summary>
        <dl className="mt-5 grid gap-5 text-sm sm:grid-cols-[11rem_minmax(0,1fr)]">
          <dt>Theorem</dt>
          <dd className="font-mono break-all">{result.theorem}</dd>
          <dt>Challenge module</dt>
          <dd className="font-mono break-all">{result.challenge_module}</dd>
          <dt>Solution module</dt>
          <dd className="font-mono break-all">{result.solution_module}</dd>
          <dt>Permitted axioms</dt>
          <dd>{comparator.permitted_axioms.length ? comparator.permitted_axioms.join(", ") : "None"}</dd>
          <dt>NanoDa check</dt>
          <dd>{comparator.enable_nanoda ? "Enabled" : "Disabled"}</dd>
        </dl>
      </details>
    </article>
  );
}
