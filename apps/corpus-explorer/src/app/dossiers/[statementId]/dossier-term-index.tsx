import Link from "next/link";

import type { Terms } from "@/lib/corpus";

/** Dossiers may reference hundreds of senses; the full text lives on their canonical pages. */
export function DossierTermIndex({ terms }: { terms: Terms }) {
  const { definitions, disambiguations } = terms;
  return (
    <section className="record-section" aria-labelledby="dossier-terms">
      <h2 id="dossier-terms" className="eyebrow">Terms and senses</h2>
      {definitions.length || disambiguations.length ? (
        <>
          <p className="mt-3 text-sm leading-6 text-[var(--muted)]">
            This dossier refers to {definitions.length} definitions and {disambiguations.length} disambiguations.
            Follow a link for its complete meaning, source basis, and resolution.
          </p>
          {definitions.length ? (
            <div className="mt-5">
              <h3 className="text-sm font-medium">Definitions</h3>
              <ul className="mt-3 flex flex-wrap gap-x-4 gap-y-2 text-sm">
                {definitions.map((definition) => (
                  <li key={definition.id}>
                    <Link className="link-quiet" href={`/definitions/${definition.id}`}>{definition.term}</Link>
                    <span className="ml-1 text-xs text-[var(--muted)]">({definition.basis})</span>
                  </li>
                ))}
              </ul>
            </div>
          ) : null}
          {disambiguations.length ? (
            <div className="mt-5">
              <h3 className="text-sm font-medium">Disambiguations</h3>
              <ul className="mt-3 flex flex-wrap gap-x-4 gap-y-2 text-sm">
                {disambiguations.map((disambiguation) => (
                  <li id={disambiguation.id} key={disambiguation.id}>
                    <Link className="link-quiet" href={`/definitions#${disambiguation.id}`}>{disambiguation.term}</Link>
                  </li>
                ))}
              </ul>
            </div>
          ) : null}
        </>
      ) : (
        <p className="mt-3 text-sm text-[var(--muted)]">No definition or disambiguation is linked yet.</p>
      )}
    </section>
  );
}
