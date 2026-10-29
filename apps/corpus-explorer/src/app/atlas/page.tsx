import type { Metadata } from "next";
import { Suspense } from "react";

import { getRegisteredConfigurationCases } from "@/lib/configuration-cases";
import { getCorpus } from "@/lib/corpus";
import { getFrontierReport } from "@/lib/site-state";
import { getVerifiedConfigurations } from "@/lib/verified-configurations";

import { AtlasExplorer } from "./atlas-explorer";
import { buildAtlasModel } from "./atlas-model";

export const metadata: Metadata = {
  title: "Progress atlas — Truth Core",
  description: "Explore certified incompatibilities, configuration families, proof routes, open premises and dependency impact.",
};

export default function AtlasPage() {
  const model = buildAtlasModel(getCorpus(), getFrontierReport());
  const verified = getVerifiedConfigurations();
  const registrations = verified ? [] : getRegisteredConfigurationCases().map(({ id, semantics, scope }) => ({ id, semantics, scope }));
  return <article className="atlas-page min-w-0">
    <header className="mb-7 border-b border-[var(--line)] pb-6">
      <p className="eyebrow">Truth Core / Research instruments</p>
      <h1 className="mt-2 font-serif text-4xl tracking-[-0.055em] sm:text-5xl">Progress atlas</h1>
      <p className="mt-3 max-w-3xl text-sm leading-6 text-[var(--muted)]">
        Five ways to inspect the same recorded evidence. Formal incompatibilities stay within their declared semantic profiles;
        open premises and proof routes remain conditional, not established conclusions.
      </p>
    </header>
    <Suspense fallback={<p className="text-sm text-[var(--muted)]">Loading atlas controls…</p>}>
      <AtlasExplorer model={model} cases={verified?.cases ?? []} producer={verified?.producer ?? null} registrations={registrations} />
    </Suspense>
  </article>;
}
