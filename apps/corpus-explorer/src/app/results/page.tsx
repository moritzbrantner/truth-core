import Link from "next/link";

import { StatusMark } from "@/components/status-mark";
import { getCorpus } from "@/lib/corpus";

export default function ResultsPage() {
  const results = getCorpus().results;

  return (
    <section className="max-w-4xl">
      <p className="eyebrow">Formal consequence</p>
      <h1 className="mt-4 font-serif text-5xl tracking-[-0.05em] sm:text-6xl">Verified arguments</h1>
      <p className="mt-6 max-w-3xl text-lg leading-8 text-[var(--muted)]">
        These records show arguments whose advertised Lean statements are checked against their solutions with the permitted axioms. They do not independently settle the fidelity of the underlying interpretations.
      </p>
      <div className="mt-12 grid gap-4">
        {results.map((result) => (
          <Link className="record-link" href={`/results/${result.id}`} key={result.id}>
            <StatusMark tone="accent">Mechanically verified argument</StatusMark>
            <h2 className="mt-4 font-serif text-3xl leading-tight tracking-[-0.03em]">{result.meaning}</h2>
            <p className="mt-4 font-mono text-xs text-[var(--muted)]">{result.id}</p>
          </Link>
        ))}
      </div>
    </section>
  );
}
