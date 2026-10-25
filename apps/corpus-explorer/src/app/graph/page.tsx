import type { Metadata } from "next";
import { Suspense } from "react";

import { PropositionGraphExplorer } from "@/components/proposition-graph-explorer";
import { getCorpus } from "@/lib/corpus";
import { getFrontierReport } from "@/lib/site-state";
import { researchFrontier } from "@/lib/research-frontier";
import { getPropositionGraph } from "@/lib/proposition-graph-data";

export const metadata: Metadata = {
  title: "Proposition graph — Truth Core",
  description:
    "Statements and explicit inference steps of the corpus, with status, tags, filters, focus mode and the paths into the root statement.",
};

export default function GraphPage() {
  const corpus = getCorpus();
  const graph = getPropositionGraph(corpus);
  const obligations = researchFrontier(corpus, graph, getFrontierReport());
  return (
    <>
      <h1 className="sr-only">Epistemic Frontier</h1>
      <Suspense fallback={<p>Loading the proposition graph…</p>}>
        <PropositionGraphExplorer graph={graph} obligations={obligations} />
      </Suspense>
    </>
  );
}
