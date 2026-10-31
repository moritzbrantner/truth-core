import type { Metadata } from "next";
import Link from "next/link";
import { Suspense } from "react";

import { buildArgumentForest } from "@/lib/argument-forest";
import { getPropositionGraph } from "@/lib/proposition-graph-data";
import { ForestExplorer } from "./forest-explorer";

export const metadata: Metadata = {
  title: "Argument forest — Truth Core",
  description: "Explore competing recorded conclusions and hypothetical premise reversals without confusing support with truth.",
};

export default function ForestPage() {
  const model = buildArgumentForest(getPropositionGraph());
  return <article className="min-w-0">
    <header className="mb-7 border-b border-[var(--line)] pb-6">
      <p className="eyebrow">Truth Core / Research instruments</p>
      <h1 className="mt-2 font-serif text-4xl tracking-[-0.055em] sm:text-5xl">Argument forest</h1>
      <p className="mt-3 max-w-3xl text-sm leading-6 text-[var(--muted)]">
        Follow the arguments supporting a conclusion, compare another recorded conclusion, or
        explore what would need reconsideration if a selected premise were false.
        Formal consequences are conditional on their premises; hypothetical reversals are not proofs.
      </p>
      <p className="mt-3 text-sm"><Link className="link-quiet" href="/atlas?view=cores">
        Inspect certified incompatibilities in the progress atlas
      </Link></p>
    </header>
    <Suspense fallback={<p className="text-sm text-[var(--muted)]">Loading argument forest…</p>}>
      <ForestExplorer model={model} />
    </Suspense>
  </article>;
}
