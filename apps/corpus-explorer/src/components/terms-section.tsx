import Link from "next/link";

import type { Corpus, TermLinks } from "@/lib/corpus";
import { findDefinition, termsFor } from "@/lib/corpus";

/**
 * The senses of the terms a record depends on, and the ambiguities it must be
 * read against (#204). A reviewer who would say "that depends on what the word
 * means" finds the meaning here.
 */
export function TermsSection({ corpus, records, title = "Terms and senses" }: { corpus: Corpus; records: TermLinks[]; title?: string }) {
  const { definitions, disambiguations } = termsFor(corpus, records);
  const used = new Set(definitions.map((definition) => definition.id));
  return (
    <section className="record-section">
      <p className="eyebrow">{title}</p>
      {definitions.length || disambiguations.length ? (
        <>
          {definitions.length ? (
            <ul className="mt-4 grid gap-3">
              {definitions.map((definition) => (
                <li key={definition.id}>
                  <Link className="font-serif text-lg hover:text-[var(--accent)]" href={`/definitions/${definition.id}`}>
                    {definition.term}
                  </Link>{" "}
                  <span className="eyebrow">{definition.basis}</span>
                  <p className="mt-1 text-sm leading-6 text-[var(--muted)]">{definition.definition}</p>
                </li>
              ))}
            </ul>
          ) : null}
          {disambiguations.map((disambiguation) => (
            <div className="mt-5 border-l-2 border-[var(--line)] pl-4" id={disambiguation.id} key={disambiguation.id}>
              <p className="eyebrow">Ambiguous term: {disambiguation.term}</p>
              <p className="mt-2 text-sm leading-6">{disambiguation.resolution}</p>
              <p className="mt-2 text-xs leading-5 text-[var(--muted)]">
                Senses:{" "}
                {disambiguation.sense_definition_ids.map((id, index) => (
                  <span key={id}>
                    {index ? " · " : ""}
                    <Link className="link-quiet" href={`/definitions/${id}`}>
                      {findDefinition(corpus, id)?.term ?? id}
                    </Link>
                    {used.has(id) ? " (used here)" : ""}
                  </span>
                ))}
                {" · "}
                <Link className="link-quiet font-mono" href={`/definitions#${disambiguation.id}`}>
                  {disambiguation.id}
                </Link>
              </p>
            </div>
          ))}
        </>
      ) : (
        <p className="mt-3 text-sm text-[var(--muted)]">No definition or disambiguation is linked yet.</p>
      )}
    </section>
  );
}
