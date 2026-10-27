import type { Corpus } from "./corpus";
import type { PropositionGraph } from "./proposition-graph";
import type { FrontierReport } from "./site-state";

export type ResearchObligation = {
  id: string;
  kind: "derivation" | "evidence" | "alternative" | "objection" | "interpretation" | "exploration";
  frontier: "knowledge" | "exploration";
  statementIds: string[];
  recordIds: string[];
  title: string;
  blocker: string;
  nextAction: string;
  rootRelevant: boolean;
  dependents: number;
  /** Targets this obligation can affect, derived from Python's route-aware upward walk. */
  goals: string[];
  href?: string;
};

/** Serializable view only: IDs are derived from corpus IDs; no persisted research store. */
export function researchFrontier(
  corpus: Corpus,
  graph: PropositionGraph,
  report: FrontierReport,
): ResearchObligation[] {
  const obligations: ResearchObligation[] = [];
  // Python's route-aware upward walk of every argument premise, open or closed;
  // a statement no argument uses has no dependents.
  const upward = (ids: string[]) => {
    const walks = ids.map((id) => report.premise_dependents[id]);
    return {
      goals: [...new Set([...ids, ...walks.flatMap((walk) => walk?.statements ?? [])])],
      dependents: new Set(walks.flatMap((walk) => walk?.arguments ?? [])).size,
    };
  };
  const add = (obligation: Omit<ResearchObligation, "rootRelevant" | "dependents" | "goals">) => {
    const reachability = upward(obligation.statementIds);
    obligations.push({
      ...obligation,
      rootRelevant: reachability.goals.includes(report.root),
      ...reachability,
    });
  };
  for (const item of report.items) {
    add({
      id: `derivation:${item.statement_id}`,
      kind: "derivation",
      frontier: "knowledge",
      statementIds: [item.statement_id],
      recordIds: item.dependent_arguments,
      title: item.paraphrase,
      blocker: item.transcription_only
        ? "Only a transcription supports this open premise; its own premises remain open."
        : "No closure rule establishes this argument premise.",
      nextAction: "Find a faithful derivation or investigate a countermodel and its missing premises.",
      href: `/dossiers/${item.statement_id}`,
    });
    if (item.depth === "bare") {
      add({
        id: `evidence:${item.statement_id}`,
        kind: "evidence",
        frontier: "knowledge",
        statementIds: [item.statement_id],
        recordIds: [],
        title: item.paraphrase,
        blocker: "No stating claim or supporting claim supplies source evidence.",
        nextAction: "Pin and materialize a source witness, or keep the statement as an explicit open premise.",
        href: `/dossiers/${item.statement_id}`,
      });
    }
    for (const alternative of item.alternatives.filter((entry) => !entry.refuted)) {
      add({
        id: `alternative:${item.statement_id}:${alternative.statement_id}`,
        kind: "alternative",
        frontier: "knowledge",
        statementIds: [item.statement_id, alternative.statement_id],
        recordIds: [alternative.statement_id],
        title: `Alternative to ${item.statement_id}`,
        blocker: `${alternative.statement_id} has no verified refutation.`,
        nextAction: "Investigate the rival's replacement account and test it against the shared questions.",
        href: `/dossiers/${alternative.statement_id}`,
      });
    }
    for (const objection of item.objections) {
      add({
        id: `objection:${item.statement_id}:${objection}`,
        kind: "objection",
        frontier: "knowledge",
        statementIds: [item.statement_id],
        recordIds: [objection],
        title: `Objection to ${item.statement_id}`,
        blocker: `${objection} is recorded as an attack; an attack is not a refutation.`,
        nextAction: "Inspect the objection and record a sourced reply or the remaining inferential bridge.",
        href: `/dossiers/${item.statement_id}`,
      });
    }
  }
  for (const claim of corpus.claims) {
    if (!claim.interpretation_of) {
      continue;
    }
    const sibling = corpus.claims.find((entry) => entry.id === claim.interpretation_of);
    add({
      id: `interpretation:${claim.id}`,
      kind: "interpretation",
      frontier: "exploration",
      statementIds: [...new Set([claim.statement_id, ...(sibling ? [sibling.statement_id] : [])])],
      recordIds: [claim.id, claim.interpretation_of],
      title: `Competing reading: ${claim.id}`,
      blocker: claim.interpretation,
      nextAction:
        "Compare the materialized passage and each reading's definitions; preserve distinct statement identities.",
      href: `/claims/${claim.id}`,
    });
  }
  for (const candidate of corpus.candidates) {
    const references = new Set(`${candidate.goal} ${candidate.reason}`.match(/\bSTMT-[A-Z0-9]+(?:-[A-Z0-9]+)*\b/g) ?? []);
    const statementIds = graph.statements
      .filter((statement) => references.has(statement.id))
      .map((statement) => statement.id);
    add({
      id: `exploration:${candidate.id}`,
      kind: "exploration",
      frontier: "exploration",
      statementIds,
      recordIds: [candidate.id],
      title: candidate.goal,
      blocker: candidate.reason,
      nextAction: `Read the queued source range ${candidate.source_id}, ${candidate.locator}. Candidate priority ${candidate.priority}; campaign decisions still govern execution.`,
      href: `/candidates/${candidate.id}`,
    });
  }
  return obligations;
}

export function orderObligations(
  obligations: ResearchObligation[],
  options: { target: string; selected: string; pins: string[]; kind: string },
) {
  const pins = new Set(options.pins);
  return obligations
    .filter(
      (item) =>
        (!options.target || item.goals.includes(options.target)) && (!options.kind || item.kind === options.kind),
    )
    .sort(
      (a, b) =>
        Number(pins.has(b.id)) - Number(pins.has(a.id)) ||
        Number(b.rootRelevant) - Number(a.rootRelevant) ||
        b.dependents - a.dependents ||
        Number(b.statementIds.includes(options.selected)) - Number(a.statementIds.includes(options.selected)) ||
        a.id.localeCompare(b.id),
    );
}
