import type { Metadata } from "next";
import { Suspense } from "react";

import { ModalExplorer } from "./modal-explorer";

export const metadata: Metadata = {
  title: "Modal logic — Truth Core",
  description: "Explore the modal cube, Kripke frames, possibility, necessity, and a Lean proof that each frame condition validates its modal axiom (the converse is not formalized).",
};

export default function ModalPage() {
  return (
    <>
      <section className="grid gap-8 lg:grid-cols-[minmax(0,1fr)_18rem] lg:items-end">
        <div>
          <p className="eyebrow">Formal logic laboratory</p>
          <h1 className="mt-4 max-w-4xl font-serif text-5xl leading-[0.95] tracking-[-0.055em] sm:text-6xl">
            Necessity and possibility, world by world.
          </h1>
          <p className="mt-6 max-w-3xl text-lg leading-8 text-[var(--muted)]">
            Explore the classical modal cube as a family of restrictions on Kripke accessibility. Move between possible worlds, change the truth of p, and inspect which modal axioms follow from the selected frame conditions.
          </p>
        </div>
        <div className="border-l border-[var(--line)] pl-5 text-sm leading-6 text-[var(--muted)]">
          <p className="eyebrow">Reference model</p>
          <p className="mt-2">
            Lean proves the frame-condition ⇒ axiom-validity direction shown here (not the converse correspondence); it is not cited as source evidence. The Stanford Encyclopedia of Philosophy&apos;s “Modal Logic” entry is background reading for the standard modal-cube terminology.
          </p>
          <a
            className="mt-3 inline-block text-[var(--ink)] underline decoration-[var(--line-strong)] underline-offset-4"
            href="https://plato.stanford.edu/entries/logic-modal/"
            rel="noreferrer"
            target="_blank"
          >
            Background: SEP “Modal Logic”
          </a>
        </div>
      </section>

      <aside className="mt-10 border-l-2 border-[var(--accent)] bg-[var(--callout)] px-5 py-5 text-sm leading-6 text-[var(--muted)]">
        <strong className="font-semibold text-[var(--ink)]">Scope.</strong> This verifies standard relational/Kripke semantics and concrete example frames. It does not assert that possible worlds are metaphysically real, nor does it yet formalize Aristotle&apos;s modal syllogistic.
      </aside>

      <Suspense fallback={<p className="mt-10 text-[var(--muted)]">Loading the modal explorer…</p>}>
        <ModalExplorer />
      </Suspense>
    </>
  );
}
