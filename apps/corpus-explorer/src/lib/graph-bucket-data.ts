import { buildGraphBuckets, type GraphBuckets } from "./graph-buckets";
import { getPropositionGraph } from "./proposition-graph-data";
import type { PropositionGraph } from "./proposition-graph";

let cached: (GraphBuckets & { graph: PropositionGraph }) | undefined;

/** Build-time /graph buckets and the whole graph they partition, computed once per build worker. */
export function getGraphBuckets() {
  if (!cached) {
    const graph = getPropositionGraph();
    cached = { ...buildGraphBuckets(graph), graph };
  }
  return cached;
}
