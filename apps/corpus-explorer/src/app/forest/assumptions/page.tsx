import type { Metadata } from "next";
import { Suspense } from "react";

import { certifiedCores } from "@/app/atlas/atlas-model";
import { buildAssumptionTree } from "@/lib/argument-forest";
import { nameOf } from "@/lib/corpus";
import { getPropositionGraph } from "@/lib/proposition-graph-data";
import { getVerifiedConfigurations } from "@/lib/verified-configurations";
import { AssumptionExplorer } from "./assumption-explorer";

export const metadata: Metadata = {
  title: "Assumption explorer — Truth Core",
  description: "Select hypothetical propositions and follow all recorded argument routes and conditional implications.",
};

export default function AssumptionsPage() {
  const model = buildAssumptionTree(getPropositionGraph());
  const verified = getVerifiedConfigurations();
  const cores = (verified?.cases ?? []).flatMap((configuration) => certifiedCores(configuration).map((core) => ({
    key: configuration.id + "::" + core.key,
    caseId: configuration.id,
    caseLabel: nameOf(configuration.id),
    resultLabels: Object.fromEntries(core.result_ids.map((id) => [id, nameOf(id)])),
    profile: `Profile ${configuration.semantics.id} · Logic ${configuration.semantics.logic} · Frame ${configuration.semantics.frame} · Domain ${configuration.semantics.domain} · Identity ${configuration.semantics.identity} · Vocabulary ${configuration.semantics.vocabulary}`,
    statementIds: core.statement_ids,
    resultIds: core.result_ids,
  })));
  return <article className="min-w-0">
    <h1 className="sr-only">Assumption explorer</h1>
    <Suspense fallback={<p className="text-sm text-[var(--muted)]">Loading proposition tree…</p>}>
      <AssumptionExplorer model={model} certifiedCores={cores} hasCertifiedEvidence={Boolean(verified)} />
    </Suspense>
  </article>;
}
