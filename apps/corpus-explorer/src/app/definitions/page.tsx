import Link from "next/link";

import { findDefinition, getCorpus } from "@/lib/corpus";

export default function DefinitionsPage() {
  const corpus = getCorpus();
  const definitions = [...corpus.definitions].sort((left, right) => left.term.localeCompare(right.term));

  return (
    <section className="max-w-4xl">
      <p className="eyebrow">Terms</p>
      <h1 className="mt-4 font-serif text-5xl tracking-[-0.05em] sm:text-6xl">Definitions and disambiguations</h1>
      <p className="mt-6 max-w-3xl text-lg leading-8 text-[var(--muted)]">
        What the words in a statement or argument mean. A definition fixes one sense of a term and is either sourced from
        claims or marked stipulative. A disambiguation lists the senses of an ambiguous term and says which sense each use
        takes, and why no argument passes from one to another.
      </p>

      <h2 className="mt-12 font-serif text-3xl tracking-[-0.03em]">Disambiguations</h2>
      <div className="mt-6 grid gap-4">
        {corpus.disambiguations.map((disambiguation) => (
          <div className="record-link" id={disambiguation.id} key={disambiguation.id}>
            <p className="eyebrow">{disambiguation.term}</p>
            <p className="mt-3 text-sm leading-6">{disambiguation.resolution}</p>
            <ul className="mt-3 grid gap-1 text-sm">
              {disambiguation.sense_definition_ids.map((id) => (
                <li key={id}>
                  <Link className="link-quiet" href={`/definitions/${id}`}>
                    {findDefinition(corpus, id)?.term ?? id}
                  </Link>
                </li>
              ))}
            </ul>
            <p className="mt-2 font-mono text-xs text-[var(--muted)]">{disambiguation.id}</p>
          </div>
        ))}
      </div>

      <h2 className="mt-12 font-serif text-3xl tracking-[-0.03em]">Definitions</h2>
      <div className="mt-6 divide-y divide-[var(--line)] border-y border-[var(--line)]">
        {definitions.map((definition) => (
          <Link className="block py-4 transition hover:text-[var(--accent)]" href={`/definitions/${definition.id}`} key={definition.id}>
            <span className="eyebrow">{definition.basis}</span>
            <span className="mt-1 block font-serif text-lg">{definition.term}</span>
            <span className="mt-1 block text-sm leading-6 text-[var(--muted)]">{definition.definition}</span>
            <span className="mt-1 block font-mono text-xs text-[var(--muted)]">{definition.id}</span>
          </Link>
        ))}
      </div>
    </section>
  );
}
