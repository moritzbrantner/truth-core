import type { Metadata } from "next";
import { Suspense } from "react";

import { PropositionGraphExplorer } from "@/components/proposition-graph-explorer";
import { getCorpus } from "@/lib/corpus";
import { getGraphBuckets } from "@/lib/graph-bucket-data";
import { getFrontierReport } from "@/lib/site-state";
import { researchFrontier } from "@/lib/research-frontier";

export const metadata: Metadata = {
  title: "Epistemic frontier — Truth Core",
  description:
    "A connected map of established propositions, conditional deductions and the open premises that form the epistemic frontier.",
};

export default function GraphPage() {
  const corpus = getCorpus();
  // The page ships only the bucket manifest; the graph itself loads in buckets (#491).
  const { graph, manifest } = getGraphBuckets();
  const obligations = researchFrontier(corpus, graph, getFrontierReport());
  const open = graph.statements.filter((statement) => statement.frontier);
  const established = graph.statements.filter((statement) => statement.established).length;
  return (
    <div className="frontier-page">
      <header className="frontier-heading">
        <div>
          <p className="eyebrow">Truth Core / Knowledge map</p>
          <h1 id="graph-heading">Epistemic frontier</h1>
          <p className="frontier-intro">Follow connected propositions to the premises that still need defending. Each highlighted dot is a real open obligation in the corpus.</p>
        </div>
        <dl className="frontier-counts">
          <div><dt>Propositions</dt><dd>{graph.statements.length}</dd></div>
          <div><dt>Established</dt><dd>{established}</dd></div>
          <div><dt>Open frontier</dt><dd>{open.length}</dd></div>
          <div><dt>Bare premises</dt><dd>{open.filter((statement) => statement.frontierDepth === "bare").length}</dd></div>
        </dl>
      </header>
      <Suspense fallback={<p>Loading the proposition graph…</p>}>
        <PropositionGraphExplorer manifest={manifest} obligations={obligations} />
      </Suspense>
    </div>
  );
}
