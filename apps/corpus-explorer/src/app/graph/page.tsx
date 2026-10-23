import type { Metadata } from "next";
import { Suspense } from "react";

import { PropositionGraphExplorer } from "@/components/proposition-graph-explorer";
import { getPropositionGraph } from "@/lib/proposition-graph-data";

export const metadata: Metadata = {
  title: "Proposition graph — Truth Core",
  description:
    "Statements and explicit inference steps of the corpus, with status, tags, filters, focus mode and the paths into the root statement.",
};

export default function GraphPage() {
  const graph = getPropositionGraph();
  const frontier = graph.statements.filter((statement) => statement.frontier).length;

  return (
    <>
      <section className="grid gap-8 lg:grid-cols-[minmax(0,1fr)_18rem] lg:items-end">
        <div>
          <p className="eyebrow">Derived view</p>
          <h1 className="mt-4 max-w-4xl font-serif text-5xl leading-[0.95] tracking-[-0.055em] sm:text-6xl">
            The proposition graph.
          </h1>
          <p className="mt-6 max-w-3xl text-lg leading-8 text-[var(--muted)]">
            Follow what a statement rests on and what it supports. The default view shows every path into{" "}
            {graph.rootPresent ? "the root statement" : "a chosen target statement"}, with open premises, the frontier,
            highlighted.
          </p>
        </div>
        <dl className="grid grid-cols-2 gap-x-6 gap-y-5 border-l border-[var(--line)] pl-5">
          <div>
            <dt className="eyebrow">Statements</dt>
            <dd className="mt-1 font-serif text-4xl">{graph.statements.length}</dd>
          </div>
          <div>
            <dt className="eyebrow">Inference steps</dt>
            <dd className="mt-1 font-serif text-4xl">{graph.inferences.length}</dd>
          </div>
          <div>
            <dt className="eyebrow">Open premises</dt>
            <dd className="mt-1 font-serif text-4xl">{frontier}</dd>
          </div>
          <div>
            <dt className="eyebrow">Arguments</dt>
            <dd className="mt-1 font-serif text-4xl">{graph.arguments.length}</dd>
          </div>
        </dl>
      </section>

      <aside className="mt-10 border-l-2 border-[var(--accent)] bg-[var(--callout)] px-5 py-5 text-sm leading-6 text-[var(--muted)]">
        <strong className="font-semibold text-[var(--ink)]">Scope.</strong> This graph is a projection of the typed corpus
        records, not a canonical model. A proved status means a Lean result checked the deduction from its premises; it
        does not make those premises true or confirm a source reading.
        {graph.rootPresent ? null : " The root statement STMT-CATHOLICISM-TRUE is not in the corpus yet, so the default target is the verified conclusion that rests on the most statements."}
      </aside>

      <Suspense fallback={<p className="mt-10 text-[var(--muted)]">Loading the proposition graph…</p>}>
        <PropositionGraphExplorer graph={graph} />
      </Suspense>
    </>
  );
}
