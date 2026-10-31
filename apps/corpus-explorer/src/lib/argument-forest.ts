import type { GraphArgument, GraphStatement, PropositionGraph } from "./proposition-graph";

/**
 * A bounded, read-only projection of the canonical corpus graph.
 * Arguments remain AND bundles of ordinary premises; multiple arguments
 * for one conclusion are OR alternatives. Nothing here computes closure.
 */
export type ForestStatus = "established" | "conditional" | "open" | "refuted" | "other";

export type ForestStatement = {
  id: string;
  paraphrase: string;
  status: ForestStatus;
  statusLabel: string;
  argumentIds: string[];
  totalArguments: number;
  directConsequences: Array<{ id: string; paraphrase: string }>;
  totalDirectConsequences: number;
  transitiveDependentArguments: number;
  rivals: Array<{ id: string; predicate: string; paraphrase: string }>;
  totalRivals: number;
};

export type ForestArgument = {
  id: string;
  meaning: string;
  premises: string[];
  resultIds: string[];
  transcriptionOnly: boolean;
};

export type ForestModel = {
  roots: Array<{ id: string; label: string }>;
  defaultGoal: string;
  defaultCompare: string;
  statements: Record<string, ForestStatement>;
  arguments: Record<string, ForestArgument>;
};

const featured: ReadonlyArray<{ id: string; label: string }> = [
  { id: "STMT-KANT-CONVERSION-NECESSARY-WITNESS", label: "Necessary individual · conditional case" },
  { id: "STMT-BRUTE-ROOT-DISJUNCTION", label: "Brute root or non-well-foundedness" },
  { id: "STMT-NECESSARY-CONCRETE-AT", label: "Necessary concrete individual" },
  { id: "STMT-NECESSARY-FACT-BOUNDARY", label: "Necessary explanatory fact" },
  { id: "STMT-EXPLANATORY-ADEQUACY-COMPARISON", label: "Explanatory adequacy" },
  { id: "STMT-CATHOLICISM-TRUE", label: "Catholicism · root case" },
];

const rivalPredicates = new Set(["alternative_to", "attacks", "refutes", "contradicts", "objects_to"]);

function statusOf(statement: GraphStatement): { status: ForestStatus; statusLabel: string } {
  if (statement.established) {
    return { status: "established", statusLabel: "Established in the recorded premise program" };
  }
  if (statement.refuted) {
    return { status: "refuted", statusLabel: "Recorded refutation" };
  }
  if (statement.frontier) {
    return { status: "open", statusLabel: "Open premise" };
  }
  if (statement.closureReason || statement.status === "proved" || statement.status === "transcription") {
    return { status: "conditional", statusLabel: "Formal consequence · premises may be open" };
  }
  return { status: "other", statusLabel: "Not established" };
}

function rankArguments(argumentsForConclusion: readonly GraphArgument[]): GraphArgument[] {
  return [...argumentsForConclusion].sort((left, right) => {
    const score = (argument: GraphArgument) =>
      Number(argument.resultIds.length > 0 && argument.transcriptionResultIds.length !== argument.resultIds.length) * 4 +
      Number(argument.resultIds.length > 0) * 2;
    return score(right) - score(left) ||
      left.premises.length - right.premises.length ||
      left.id.localeCompare(right.id);
  });
}

/** Returns only records referenced by a small, navigable set of conclusions. */
export function buildArgumentForest(
  graph: PropositionGraph,
  preferredRoots: ReadonlyArray<{ id: string; label: string }> = featured,
): ForestModel {
  const byId = new Map(graph.statements.map((statement) => [statement.id, statement]));
  const argumentsByConclusion = new Map<string, GraphArgument[]>();
  const argumentsUsingPremise = new Map<string, GraphArgument[]>();
  for (const argument of graph.arguments) {
    argumentsByConclusion.set(argument.conclusion, [
      ...(argumentsByConclusion.get(argument.conclusion) ?? []), argument,
    ]);
    for (const premise of new Set(argument.premises)) {
      argumentsUsingPremise.set(premise, [...(argumentsUsingPremise.get(premise) ?? []), argument]);
    }
  }
  const namedRoots = preferredRoots.filter((root) => byId.has(root.id));
  const fallback = graph.statements
    .filter((statement) => (argumentsByConclusion.get(statement.id)?.length ?? 0) > 0)
    .sort((left, right) =>
      Number(right.reachesRoot) - Number(left.reachesRoot) ||
      right.transitiveDependentArguments - left.transitiveDependentArguments ||
      left.id.localeCompare(right.id));
  const roots = [...namedRoots];
  for (const statement of fallback) {
    if (roots.length >= 8) { break; }
    if (!roots.some((root) => root.id === statement.id)) {
      roots.push({ id: statement.id, label: statement.paraphrase });
    }
  }
  if (!roots.length && graph.statements[0]) {
    roots.push({ id: graph.statements[0].id, label: graph.statements[0].paraphrase });
  }

  const visible = new Set<string>();
  const includedArguments = new Map<string, GraphArgument>();
  const visitedDepth = new Map<string, number>();
  const queue = roots.map((root) => ({ id: root.id, depth: 0 }));
  while (queue.length && visible.size < 1000) {
    const next = queue.shift()!;
    const statement = byId.get(next.id);
    if (!statement) { continue; }
    visible.add(next.id);
    if ((visitedDepth.get(next.id) ?? Infinity) <= next.depth) { continue; }
    visitedDepth.set(next.id, next.depth);
    if (next.depth >= 3) { continue; }
    for (const argument of rankArguments(argumentsByConclusion.get(next.id) ?? []).slice(0, 2)) {
      includedArguments.set(argument.id, argument);
      for (const premise of argument.premises) {
        queue.push({ id: premise, depth: next.depth + 1 });
      }
    }
  }

  const links = new Map<string, Array<{ id: string; predicate: string }>>();
  for (const relation of graph.relations) {
    if (!rivalPredicates.has(relation.predicate)) { continue; }
    if (!byId.has(relation.subject) || !byId.has(relation.object) || relation.subject === relation.object) { continue; }
    for (const [from, to] of [[relation.subject, relation.object], [relation.object, relation.subject]]) {
      links.set(from, [...(links.get(from) ?? []), { id: to, predicate: relation.predicate }]);
    }
  }

  // Rival references are navigable, but merely linked records never become proof edges.
  const originalVisible = [...visible];
  for (const id of originalVisible) {
    for (const rival of (links.get(id) ?? []).slice(0, 5)) {
      visible.add(rival.id);
    }
  }

  const statements: Record<string, ForestStatement> = {};
  for (const id of visible) {
    const statement = byId.get(id);
    if (!statement) { continue; }
    const consequences = [...new Set((argumentsUsingPremise.get(id) ?? []).map((argument) => argument.conclusion))]
      .sort()
      .filter((other) => byId.has(other));
    const rivals = [...new Map((links.get(id) ?? []).map((entry) => [entry.id + ":" + entry.predicate, entry])).values()]
      .sort((a, b) => a.id.localeCompare(b.id) || a.predicate.localeCompare(b.predicate));
    statements[id] = {
      id,
      paraphrase: statement.paraphrase,
      ...statusOf(statement),
      argumentIds: rankArguments(argumentsByConclusion.get(id) ?? [])
        .filter((argument) => includedArguments.has(argument.id))
        .map((argument) => argument.id),
      totalArguments: argumentsByConclusion.get(id)?.length ?? 0,
      directConsequences: consequences.slice(0, 6).map((other) => ({
        id: other,
        paraphrase: byId.get(other)!.paraphrase,
      })),
      totalDirectConsequences: consequences.length,
      transitiveDependentArguments: statement.transitiveDependentArguments,
      rivals: rivals.slice(0, 5).map((rival) => ({
        id: rival.id,
        predicate: rival.predicate,
        paraphrase: byId.get(rival.id)!.paraphrase,
      })),
      totalRivals: rivals.length,
    };
  }

  const argumentsMap: Record<string, ForestArgument> = {};
  for (const argument of includedArguments.values()) {
    argumentsMap[argument.id] = {
      id: argument.id,
      meaning: argument.meaning,
      premises: argument.premises,
      resultIds: argument.resultIds,
      transcriptionOnly: argument.resultIds.length > 0 &&
        argument.resultIds.every((id) => argument.transcriptionResultIds.includes(id)),
    };
  }

  return {
    roots,
    defaultGoal: roots[0]?.id ?? "",
    defaultCompare: roots.find((root) => root.id !== roots[0]?.id)?.id ?? "",
    statements,
    arguments: argumentsMap,
  };
}
