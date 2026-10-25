import type { PropositionGraph } from "./proposition-graph";

export type ProofExplorationOptions = {
  target: string;
  /** Restrict available established facts, never promote open statements to facts. */
  scope?: readonly string[];
  budget: number;
  signal?: AbortSignal;
};

export type ProofJoin = {
  statementId: string;
  status: "proposed";
  argumentIds: string[];
  remainingStatementIds: string[];
};

export type ProofBranch = {
  inferenceId: string;
  output: string;
  requiredStatementIds: string[];
  remainingStatementIds: string[];
  scopedAssumptionIds: string[];
  dischargedStatementIds: string[];
  resultIds: string[];
};

export type ProofExploration = {
  target: string;
  status: "complete" | "budget-exhausted" | "cancelled";
  visits: number;
  establishedStatementIds: string[];
  /** Proposed compositions only. Neither these nor joins update corpus closure. */
  forwardStatementIds: string[];
  backwardStatementIds: string[];
  forwardArgumentIds: string[];
  backwardInferenceIds: string[];
  branches: ProofBranch[];
  joins: ProofJoin[];
};

const sorted = (ids: Iterable<string>) => [...new Set(ids)].sort();

/**
 * Bounded exact-ID exploration over the existing graph. One yield is one budgeted
 * work item, letting callers return to the browser event loop and cancel. Seeds
 * come exclusively from corpus.py's established projection. Checked argument
 * boundaries, rather than individual unchecked inference edges, govern forward
 * proposals: their complete premises must be available. A proposal still needs
 * Lean/Comparator/NanoDa composition and exact premise bindings before recording.
 *
 * Per-run visited keys are (goal, selected scope, available premises). No cache
 * survives corpus/goal changes. Backward branches are OR alternatives containing
 * AND obligations. Scoped assumptions stay local; they never seed forward search.
 */
export function* exploreProof(
  graph: PropositionGraph,
  options: ProofExplorationOptions,
): Generator<void, ProofExploration> {
  const scope = options.scope ? new Set(options.scope) : null;
  const seeds = sorted(
    graph.statements.filter((s) => s.established && (!scope || scope.has(s.id))).map((s) => s.id),
  );
  const available = new Set(seeds);
  const backward = new Set<string>();
  const forwardArguments = new Set<string>();
  const branches: ProofBranch[] = [];
  const witnesses = new Map<string, string[]>();
  const visited = new Set<string>();
  const budget = Number.isFinite(options.budget) ? Math.max(0, Math.min(10000, Math.floor(options.budget))) : 0;
  let visits = 0;
  let status: ProofExploration["status"] = "complete";
  const step = () => {
    if (options.signal?.aborted) {
      status = "cancelled";
      return false;
    }
    if (visits >= budget) {
      status = "budget-exhausted";
      return false;
    }
    visits += 1;
    return true;
  };
  const checked = graph.arguments.filter((a) => a.resultIds.length > 0).sort((a, b) => a.id.localeCompare(b.id));
  // The finite least fixpoint starts at independently established facts. No
  // ungrounded reciprocal cycle can enter it. This is search, not closure.
  let changed = true;
  while (changed && status === "complete") {
    changed = false;
    for (const argument of checked) {
      const key = JSON.stringify(["forward", argument.id, seeds, sorted(available)]);
      if (visited.has(key)) {
        continue;
      }
      if (!step()) {
        break;
      }
      yield;
      visited.add(key);
      if (argument.premises.every((id) => available.has(id))) {
        forwardArguments.add(argument.id);
        if (!available.has(argument.conclusion)) {
          available.add(argument.conclusion);
          witnesses.set(argument.conclusion, sorted([
            ...argument.premises.flatMap((id) => witnesses.get(id) ?? []),
            argument.id,
          ]));
          changed = true;
        }
      }
    }
  }
  const producers = new Map<string, PropositionGraph["inferences"]>();
  for (const inference of [...graph.inferences].sort((a, b) => a.id.localeCompare(b.id))) {
    const entries = producers.get(inference.output) ?? [];
    entries.push(inference);
    producers.set(inference.output, entries);
  }
  const queue = [options.target];
  for (let cursor = 0; cursor < queue.length && status === "complete"; cursor += 1) {
    const goal = queue[cursor];
    const key = JSON.stringify(["backward", goal, seeds, sorted(available)]);
    if (visited.has(key)) {
      continue;
    }
    if (!step()) {
      break;
    }
    yield;
    visited.add(key);
    backward.add(goal);
    // Retain decompositions even for established goals so the intermediate
    // junction and proof provenance remain inspectable.
    for (const inference of producers.get(goal) ?? []) {
      if (!step()) {
        break;
      }
      yield;
      const required = sorted([...inference.inputs, ...inference.assumptions]);
      branches.push({
        inferenceId: inference.id,
        output: goal,
        requiredStatementIds: required,
        remainingStatementIds: required.filter((id) => !available.has(id) || inference.assumptions.includes(id)),
        scopedAssumptionIds: inference.assumptions,
        dischargedStatementIds: inference.discharged,
        resultIds: sorted(graph.arguments.filter((a) => inference.argumentIds.includes(a.id)).flatMap((a) => a.resultIds)),
      });
      queue.push(...required.filter((id) => !inference.assumptions.includes(id)));
    }
  }
  const joins = sorted([...backward].filter((id) => available.has(id))).map((statementId): ProofJoin => ({
    statementId,
    status: "proposed",
    argumentIds: witnesses.get(statementId) ?? [],
    remainingStatementIds: sorted(branches.filter((b) => b.requiredStatementIds.includes(statementId)).flatMap((b) => b.remainingStatementIds)),
  }));
  return {
    target: options.target,
    status,
    visits,
    establishedStatementIds: seeds,
    forwardStatementIds: sorted(available),
    backwardStatementIds: sorted(backward),
    forwardArgumentIds: sorted(forwardArguments),
    backwardInferenceIds: sorted(branches.map((b) => b.inferenceId)),
    branches,
    joins,
  };
}

export function runProofExploration(graph: PropositionGraph, options: ProofExplorationOptions): ProofExploration {
  const search = exploreProof(graph, options);
  let next = search.next();
  while (!next.done) {
    next = search.next();
  }
  return next.value;
}

export type IntermediateLemmaCandidate = {
  status: "unverified";
  target: string;
  wording: string;
  formalization: "unformalized";
  intendedBridge: { fromStatementIds: string[]; toStatementId: string };
  missingPremiseIds: string[];
  needs: string[];
  provenance: { method: "exact-statement-id-exploration"; visits: number; inferenceIds: string[]; argumentIds: string[] };
};

/**
 * A transient research suggestion, never a corpus statement or invented witness.
 * Exact reuse runs first. Bounded/cancelled search cannot establish that reuse
 * failed, so it never triggers invention. Source-range candidates still govern
 * actual research; this only exposes the remaining obligation in that view.
 */
export function suggestIntermediateLemma(result: ProofExploration): IntermediateLemmaCandidate | null {
  if (result.status !== "complete" || result.forwardStatementIds.includes(result.target)) {
    return null;
  }
  const produced = new Set(result.branches.map((branch) => branch.output));
  const missing = sorted(result.branches.flatMap((branch) => branch.remainingStatementIds).filter((id) => !produced.has(id)));
  return {
    status: "unverified",
    target: result.target,
    wording: `Investigate an intermediate lemma connecting the established scope to ${result.target}. No entailment or formal statement has been supplied.`,
    formalization: "unformalized",
    intendedBridge: { fromStatementIds: result.establishedStatementIds, toStatementId: result.target },
    missingPremiseIds: missing,
    needs: [
      "A precise Lean proposition and an explicit inference with every required premise.",
      "Definition and disambiguation records for every load-bearing term and reading.",
      "A pinned, materialized source-range witness for any source-derived reading; empirical premises remain open until independently defended.",
      "Lean, exact premise binding, Comparator and NanoDa verification before recording a result; source fidelity remains a separate judgment.",
    ],
    provenance: { method: "exact-statement-id-exploration", visits: result.visits, inferenceIds: result.backwardInferenceIds, argumentIds: result.forwardArgumentIds },
  };
}

/** Adds a transient suggestion to the existing derived research queue. */
export function lemmaResearchObligation(result: ProofExploration, root: string): import("./research-frontier").ResearchObligation | null {
  const candidate = suggestIntermediateLemma(result);
  if (!candidate) {
    return null;
  }
  return {
    id: `exploration:proposed-lemma:${candidate.target}`,
    kind: "exploration",
    frontier: "exploration",
    statementIds: sorted([candidate.target, ...candidate.missingPremiseIds]),
    recordIds: candidate.provenance.inferenceIds,
    title: `Unverified intermediate lemma for ${candidate.target}`,
    blocker: candidate.wording,
    nextAction: candidate.needs.join(" "),
    rootRelevant: candidate.target === root,
    dependents: 0,
    goals: [candidate.target],
  };
}
