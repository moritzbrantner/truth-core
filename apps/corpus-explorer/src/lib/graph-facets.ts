import { NO_LEAN_AREA } from "./graph-areas";
import type { GraphStatement } from "./proposition-graph";

/**
 * Filter facets of a graph statement (#491). Every value is read from fields the
 * proposition graph already projects from the corpus records and the Python
 * frontier report; nothing here decides closure or reachability itself.
 */

export type ClosureFacet = "established" | "conditional" | "frontier-bare" | "frontier-sourced" | "unclosed";
export type RecordFacet = "claim" | "argument" | "result" | "inference" | "relation";
export type ReachFacet = "root" | "other";

export const CLOSURE_FACETS: ReadonlyArray<{ id: ClosureFacet; label: string; description: string }> = [
  { id: "established", label: "Established", description: "In established_statements of corpus.py frontier." },
  { id: "conditional", label: "Closed · conditional", description: "Closed by corpus.py frontier but resting on open premises." },
  { id: "frontier-bare", label: "Frontier · bare", description: "Open premise that no claim states and no supports relation backs." },
  { id: "frontier-sourced", label: "Frontier · sourced", description: "Open premise that a claim or supports relation backs." },
  { id: "unclosed", label: "Not closed, off the frontier", description: "Neither closed nor an open argument premise (for example a source reading no argument uses)." },
];

export const RECORD_FACETS: ReadonlyArray<{ id: RecordFacet; label: string; description: string }> = [
  { id: "claim", label: "Source claim", description: "A claim record states it." },
  { id: "argument", label: "Argument", description: "Premise or conclusion of an argument record." },
  { id: "result", label: "Result", description: "Conclusion of an argument with a verification result." },
  { id: "inference", label: "Inference", description: "Input, assumption or output of an inference application." },
  { id: "relation", label: "Research link", description: "Endpoint of a recorded non-inferential relation." },
];

export const REACH_FACETS: ReadonlyArray<{ id: ReachFacet; label: string }> = [
  { id: "root", label: "Reaches the root" },
  { id: "other", label: "Does not reach the root" },
];

export function closureOf(statement: GraphStatement): ClosureFacet {
  if (statement.established) return "established";
  if (statement.closureReason) return "conditional";
  if (statement.frontier) return statement.frontierDepth === "bare" ? "frontier-bare" : "frontier-sourced";
  return "unclosed";
}

export const reachOf = (statement: GraphStatement): ReachFacet => (statement.reachesRoot ? "root" : "other");
export const areaOf = (statement: GraphStatement) => statement.area ?? NO_LEAN_AREA;
export const laneOf = (statement: GraphStatement) => statement.lane ?? "none";

type Adjacency = {
  producers: Map<string, unknown>;
  consumers: Map<string, unknown>;
  researchNeighbors: Map<string, unknown>;
};

export function recordKindsOf(statement: GraphStatement, index: Adjacency): RecordFacet[] {
  const kinds: RecordFacet[] = [];
  if (statement.claims.length) kinds.push("claim");
  if (statement.premiseOf.length || statement.conclusionOf.length) kinds.push("argument");
  if (statement.verifyingResultIds.length) kinds.push("result");
  if (index.producers.has(statement.id) || index.consumers.has(statement.id)) kinds.push("inference");
  if (index.researchNeighbors.has(statement.id)) kinds.push("relation");
  return kinds;
}
