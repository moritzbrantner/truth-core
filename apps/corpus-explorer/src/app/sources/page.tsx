import Link from "next/link";

import { getCorpus } from "@/lib/corpus";

export default function SourcesPage() {
  const sources = getCorpus().sources.sort(
    (left, right) => left.author.localeCompare(right.author) || left.work.localeCompare(right.work),
  );

  return (
    <section className="max-w-4xl">
      <p className="eyebrow">Primary texts</p>
      <h1 className="mt-4 font-serif text-5xl tracking-[-0.05em] sm:text-6xl">Sources</h1>
      <p className="mt-6 max-w-2xl text-lg leading-8 text-[var(--muted)]">
        Each claim points to a stable source record and a conventional classical locator.
      </p>
      <div className="mt-12 divide-y divide-[var(--line)] border-y border-[var(--line)]">
        {sources.map((source) => (
          <Link className="group grid gap-3 py-6 sm:grid-cols-[12rem_minmax(0,1fr)]" href={`/sources/${source.id}`} key={source.id}>
            <p className="text-sm text-[var(--muted)]">{source.citation_system}</p>
            <div>
              <h2 className="font-serif text-3xl tracking-[-0.03em] group-hover:text-[var(--accent)]">
                {source.author}, <em>{source.work}</em>
              </h2>
              <p className="mt-2 text-sm leading-6 text-[var(--muted)]">{source.notes}</p>
            </div>
          </Link>
        ))}
      </div>
    </section>
  );
}
