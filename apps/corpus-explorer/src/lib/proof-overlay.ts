import type { ProofExploration } from "./proof-exploration";
import type { PropositionGraph } from "./proposition-graph";

export type ProofOverlay = {
  target: boolean;
  established: boolean;
  forward: boolean;
  backward: boolean;
  junction: boolean;
  blocker: boolean;
};

/** Additive styling/inspection flags keyed by existing IDs; no graph mutations. */
export function proofOverlay(graph: PropositionGraph, result: ProofExploration | null): Map<string, ProofOverlay> {
  const flags = new Map<string, ProofOverlay>();
  if (!result) {
    return flags;
  }
  const mark = (ids: Iterable<string>, key: keyof ProofOverlay) => {
    for (const id of ids) {
      const value = flags.get(id) ?? { target: false, established: false, forward: false, backward: false, junction: false, blocker: false };
      value[key] = true;
      flags.set(id, value);
    }
  };
  mark([result.target], "target");
  mark(result.establishedStatementIds, "established");
  mark(result.forwardStatementIds, "forward");
  mark(result.backwardStatementIds, "backward");
  mark(result.backwardInferenceIds, "backward");
  const forwardArguments = new Set(result.forwardArgumentIds);
  mark(graph.arguments.filter((a) => forwardArguments.has(a.id)).flatMap((a) => a.inferenceIds), "forward");
  mark(result.joins.map((join) => join.statementId), "junction");
  mark(result.branches.flatMap((branch) => branch.remainingStatementIds), "blocker");
  return flags;
}
