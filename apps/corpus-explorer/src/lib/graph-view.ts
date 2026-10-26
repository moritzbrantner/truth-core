import { hasFilters, type GraphState } from "./graph-state";
import type { GraphInference, GraphStatement, PropositionGraph } from "./proposition-graph";

/** Root-path and focus views keep at most this many statements, nearest first. */
export const MAX_VIEW_STATEMENTS = 300;

export type ViewStatementNode = {
  kind: "statement";
  id: string;
  statement: GraphStatement;
  matched: boolean;
  highlighted: boolean;
  anchor: boolean;
};

export type ViewInferenceNode = {
  kind: "inference";
  id: string;
  inference: GraphInference;
  matched: boolean;
  highlighted: boolean;
  anchor: boolean;
};

export type ViewClusterNode = {
  kind: "cluster";
  id: string;
  key: string;
  label: string;
  size: number;
  matchCount: number;
  frontierCount: number;
};

export type ViewNode = ViewStatementNode | ViewInferenceNode | ViewClusterNode;

export type ViewEdgeKind = "premise" | "assumption" | "conclusion" | "relation" | "cluster";

export type ViewEdge = {
  id: string;
  source: string;
  target: string;
  kind: ViewEdgeKind;
  label?: string;
  count?: number;
  highlighted: boolean;
};

export type GraphViewModel = {
  nodes: ViewNode[];
  edges: ViewEdge[];
  /** Statement (or inference) the view is built around, if any. */
  anchor: string | null;
  statementCount: number;
  frontierCount: number;
  /** Statements left out because of MAX_VIEW_STATEMENTS. */
  truncated: number;
  message?: string;
};

export type GraphIndex = {
  statementById: Map<string, GraphStatement>;
  inferenceById: Map<string, GraphInference>;
  consumers: Map<string, GraphInference[]>;
  producers: Map<string, GraphInference[]>;
};

export const clusterNodeId = (key: string) => `cluster:${key}`;

export function indexGraph(graph: PropositionGraph): GraphIndex {
  const consumers = new Map<string, GraphInference[]>();
  const producers = new Map<string, GraphInference[]>();
  for (const inference of graph.inferences) {
    for (const input of new Set([...inference.inputs, ...inference.assumptions])) {
      consumers.set(input, [...(consumers.get(input) ?? []), inference]);
    }
    producers.set(inference.output, [...(producers.get(inference.output) ?? []), inference]);
  }
  return {
    statementById: new Map(graph.statements.map((statement) => [statement.id, statement])),
    inferenceById: new Map(graph.inferences.map((inference) => [inference.id, inference])),
    consumers,
    producers,
  };
}

function inferenceStatements(inference: GraphInference) {
  return [...inference.inputs, ...inference.assumptions, inference.output];
}

export function statementMatches(statement: GraphStatement, state: GraphState, index: GraphIndex) {
  if (state.leaf === "unsupported" && index.producers.has(statement.id)) { return false; }
  if (state.leaf === "unconsumed" && index.consumers.has(statement.id)) { return false; }
  if (state.leaf === "frontier" && !statement.frontier) { return false; }
  const query = state.q.trim().toLowerCase();
  if (
    query &&
    ![statement.id, statement.paraphrase, statement.leanDeclaration ?? ""].some((text) =>
      text.toLowerCase().includes(query),
    )
  ) {
    return false;
  }
  if (state.status.length && !state.status.includes(statement.status)) {
    return false;
  }
  if (state.source && !statement.sourceIds.includes(state.source)) {
    return false;
  }
  return state.tags.every((tag) => statement.tags.includes(tag));
}

/** Matches across the whole corpus, for the search list next to the graph. */
export function searchStatements(graph: PropositionGraph, state: GraphState, limit = 25, index: GraphIndex = indexGraph(graph)) {
  if (!hasFilters(state)) {
    return { total: 0, items: [] as GraphStatement[] };
  }
  const matches = graph.statements
    .filter((statement) => statementMatches(statement, state, index))
    .sort(
      (left, right) =>
        Number(right.frontier) - Number(left.frontier) ||
        right.transitiveDependentArguments - left.transitiveDependentArguments ||
        left.id.localeCompare(right.id),
    );
  return { total: matches.length, items: matches.slice(0, limit) };
}

type Selection = { statements: string[]; inferences: string[] };

/** Everything on inference paths into `target`: what it rests on, transitively. */
export function rootPathSelection(index: GraphIndex, target: string): Selection {
  const statements = [target];
  const seenStatements = new Set(statements);
  const inferences: string[] = [];
  const seenInferences = new Set<string>();
  for (let cursor = 0; cursor < statements.length; cursor += 1) {
    for (const inference of index.producers.get(statements[cursor]) ?? []) {
      if (seenInferences.has(inference.id)) continue;
      seenInferences.add(inference.id);
      inferences.push(inference.id);
      for (const id of [...inference.inputs, ...inference.assumptions]) {
        if (!seenStatements.has(id)) {
          seenStatements.add(id);
          statements.push(id);
        }
      }
    }
  }
  return { statements, inferences };
}

/**
 * A node plus N inference hops upward (what it supports) and/or downward
 * (what it rests on). Every included inference brings all its premises and its
 * conclusion, so no step is shown with a premise missing.
 */
export function focusSelection(index: GraphIndex, node: string, hops: number, dir: GraphState["dir"]): Selection {
  const statementOrder: string[] = [];
  const seenStatements = new Set<string>();
  const inferenceOrder: string[] = [];
  const seenInferences = new Set<string>();
  const addStatement = (id: string) => {
    if (!seenStatements.has(id)) {
      seenStatements.add(id);
      statementOrder.push(id);
    }
  };
  const addInference = (inference: GraphInference) => {
    if (!seenInferences.has(inference.id)) {
      seenInferences.add(inference.id);
      inferenceOrder.push(inference.id);
    }
  };

  const centreInference = index.inferenceById.get(node);
  if (centreInference) {
    addInference(centreInference);
  } else {
    addStatement(node);
  }

  const walk = (direction: "up" | "down") => {
    let layer: string[] = centreInference
      ? direction === "up"
        ? [centreInference.output]
        : [...centreInference.inputs, ...centreInference.assumptions]
      : [node];
    const visited = new Set(layer);
    const remaining = centreInference ? hops - 1 : hops;
    for (let hop = 0; hop < remaining; hop += 1) {
      const next: string[] = [];
      for (const statementId of layer) {
        const steps = (direction === "up" ? index.consumers : index.producers).get(statementId) ?? [];
        for (const inference of steps) {
          addInference(inference);
          const far = direction === "up" ? [inference.output] : [...inference.inputs, ...inference.assumptions];
          for (const id of far) {
            if (!visited.has(id)) {
              visited.add(id);
              next.push(id);
            }
          }
        }
      }
      layer = next;
    }
  };
  if (dir !== "down") walk("up");
  if (dir !== "up") walk("down");

  for (const inferenceId of inferenceOrder) {
    const inference = index.inferenceById.get(inferenceId);
    if (inference) inferenceStatements(inference).forEach(addStatement);
  }
  return { statements: statementOrder, inferences: inferenceOrder };
}

function clusterLabel(graph: PropositionGraph, state: GraphState, key: string) {
  if (state.cluster === "source") {
    const source = graph.sources.find((entry) => entry.id === key);
    if (source) return `${source.author}, ${source.work}`;
  }
  return key;
}

export function computeGraphView(
  graph: PropositionGraph,
  state: GraphState,
  index: GraphIndex = indexGraph(graph),
): GraphViewModel {
  const filtering = hasFilters(state);
  const highlightArgument = graph.arguments.find((argument) => argument.id === state.arg);
  const highlightedStatements = new Set(
    highlightArgument ? [...highlightArgument.premises, highlightArgument.conclusion] : [],
  );
  const highlightedInferences = new Set(highlightArgument?.inferenceIds ?? []);
  // A queue, search result, proof pin, or restored URL may point to a reading
  // without an inference yet. Keep that explicitly addressed dot on the map.
  const explicitlyShown = new Set([
    state.sel,
    state.node,
    state.target,
    ...state.expanded,
    ...state.pins,
    ...highlightedStatements,
  ]);
  const matches = (id: string) => {
    const statement = index.statementById.get(id);
    return !filtering || (statement ? statementMatches(statement, state, index) : false);
  };

  let anchor: string | null = null;
  let selection: Selection;
  if (state.view === "all") {
    selection = {
      statements: graph.statements
        .filter((statement) =>
          state.layout !== "network" ||
          state.showIsolated ||
          index.producers.has(statement.id) ||
          index.consumers.has(statement.id) ||
          explicitlyShown.has(statement.id) ||
          (filtering && statementMatches(statement, state, index)),
        )
        .map((statement) => statement.id),
      inferences: graph.inferences.map((inference) => inference.id),
    };
  } else if (state.view === "focus") {
    anchor = state.node || state.sel || state.target || graph.defaultTarget;
    if (!anchor || (!index.statementById.has(anchor) && !index.inferenceById.has(anchor))) {
      return emptyView(anchor, "Choose a statement or inference to focus on.");
    }
    selection = focusSelection(index, anchor, state.hops, state.dir);
  } else {
    anchor = state.target || graph.defaultTarget;
    if (!anchor || !index.statementById.has(anchor)) {
      return emptyView(anchor, `Unknown target statement ${anchor ?? ""}.`.trim());
    }
    selection = rootPathSelection(index, anchor);
  }

  // Explicit expansions are in-place, bounded one-hop additions. Sets retain shared identity and cycles.
  if (state.view !== "all") {
    const selectedStatements = new Set(selection.statements);
    const selectedInferences = new Set(selection.inferences);
    for (const id of state.expanded) {
      const extra = focusSelection(index, id, 1, "both");
      extra.statements.forEach((entry) => selectedStatements.add(entry));
      extra.inferences.forEach((entry) => selectedInferences.add(entry));
    }
    selection = { statements: [...selectedStatements], inferences: [...selectedInferences] };
  }

  let statementIds = selection.statements.filter((id) => index.statementById.has(id));
  if (state.hide && filtering) {
    const shown = new Set(statementIds.filter((id) => id === anchor || explicitlyShown.has(id) || matches(id)));
    // A step whose conclusion and some premise survive brings back its other
    // premises as (dimmed) context, so no step is drawn with a premise missing.
    for (const id of selection.inferences) {
      const inference = index.inferenceById.get(id);
      if (!inference || !shown.has(inference.output)) continue;
      const premises = [...inference.inputs, ...inference.assumptions];
      if (premises.some((premise) => shown.has(premise))) premises.forEach((premise) => shown.add(premise));
    }
    statementIds = statementIds.filter((id) => shown.has(id));
  }
  let truncated = 0;
  if (state.view !== "all" && statementIds.length > MAX_VIEW_STATEMENTS) {
    truncated = statementIds.length - MAX_VIEW_STATEMENTS;
    statementIds = statementIds.slice(0, MAX_VIEW_STATEMENTS);
  }
  const kept = new Set(statementIds);
  const inferences = selection.inferences.flatMap((id) => {
    const inference = index.inferenceById.get(id);
    if (!inference || !kept.has(inference.output)) return [];
    // Draw a step only with all of its premises (invariant 10: no partial arguments).
    if (![...inference.inputs, ...inference.assumptions].every((input) => kept.has(input))) {
      return [];
    }
    return [inference];
  });

  // In the full view, collapsed clusters stand in for their statements.
  const openClusters = new Set(state.open);
  if (state.view === "all") {
    for (const id of state.expanded) {
      for (const related of focusSelection(index, id, 1, "both").statements) {
        const statement = index.statementById.get(related);
        if (statement) {
          openClusters.add(statement.clusters[state.cluster]);
        }
      }
    }
  }
  const representative = (id: string) => {
    if (state.view !== "all" || state.layout === "network") return id;
    const statement = index.statementById.get(id) as GraphStatement;
    const key = statement.clusters[state.cluster];
    return openClusters.has(key) ? id : clusterNodeId(key);
  };

  const nodes: ViewNode[] = [];
  const clusters = new Map<string, ViewClusterNode>();
  let frontierCount = 0;
  for (const id of statementIds) {
    const statement = index.statementById.get(id) as GraphStatement;
    if (statement.frontier) frontierCount += 1;
    const rep = representative(id);
    if (rep === id) {
      nodes.push({
        kind: "statement",
        id,
        statement,
        matched: matches(id),
        highlighted: highlightedStatements.has(id),
        anchor: id === anchor,
      });
      continue;
    }
    const key = statement.clusters[state.cluster];
    const cluster = clusters.get(rep) ?? {
      kind: "cluster" as const,
      id: rep,
      key,
      label: clusterLabel(graph, state, key),
      size: 0,
      matchCount: 0,
      frontierCount: 0,
    };
    cluster.size += 1;
    if (matches(id)) cluster.matchCount += 1;
    if (statement.frontier) cluster.frontierCount += 1;
    clusters.set(rep, cluster);
  }
  const visibleClusters = [...clusters.values()]
    .filter((cluster) => !(state.hide && filtering && cluster.matchCount === 0))
    .sort((left, right) => left.key.localeCompare(right.key));
  nodes.push(...visibleClusters);
  const visible = new Set(nodes.map((node) => node.id));

  const edges: ViewEdge[] = [];
  const clusterEdges = new Map<string, ViewEdge>();
  for (const inference of inferences) {
    const output = representative(inference.output);
    if (!visible.has(output)) continue;
    const roles: Array<[string[], ViewEdgeKind]> = [
      [inference.inputs, "premise"],
      [inference.assumptions, "assumption"],
    ];
    if (output !== inference.output) {
      // Conclusion inside a collapsed cluster: summarize the step as a cluster link,
      // counted once per step and source cluster.
      const counted = new Set<string>();
      for (const [ids] of roles) {
        for (const input of ids) {
          const source = representative(input);
          if (!kept.has(input) || !visible.has(source) || source === output || counted.has(source)) continue;
          counted.add(source);
          const id = `${source}=>${output}`;
          const existing = clusterEdges.get(id);
          if (existing) {
            existing.count = (existing.count ?? 1) + 1;
          } else {
            clusterEdges.set(id, { id, source, target: output, kind: "cluster", count: 1, highlighted: false });
          }
        }
      }
      continue;
    }
    nodes.push({
      kind: "inference",
      id: inference.id,
      inference,
      matched: matches(inference.output) || [...inference.inputs, ...inference.assumptions].some(matches),
      highlighted: highlightedInferences.has(inference.id),
      anchor: inference.id === anchor,
    });
    visible.add(inference.id);
    const seen = new Set<string>();
    for (const [ids, kind] of roles) {
      for (const input of ids) {
        const source = representative(input);
        if (!kept.has(input) || !visible.has(source) || seen.has(source)) continue;
        seen.add(source);
        edges.push({
          id: `${source}->${inference.id}`,
          source,
          target: inference.id,
          kind,
          highlighted: highlightedInferences.has(inference.id),
        });
      }
    }
    edges.push({
      id: `${inference.id}->${inference.output}`,
      source: inference.id,
      target: inference.output,
      kind: "conclusion",
      highlighted: highlightedInferences.has(inference.id),
    });
  }
  for (const edge of clusterEdges.values()) {
    edge.label = `${edge.count} step${edge.count === 1 ? "" : "s"}`;
    edges.push(edge);
  }
  for (const relation of state.relations ? graph.relations : []) {
    if (visible.has(relation.subject) && visible.has(relation.object)) {
      edges.push({
        id: `relation:${relation.id}`,
        source: relation.subject,
        target: relation.object,
        kind: "relation",
        label: relation.predicate.replaceAll("_", " "),
        highlighted: false,
      });
    }
  }

  return {
    nodes,
    edges,
    anchor,
    statementCount: statementIds.length,
    frontierCount,
    truncated,
    message:
      state.view === "all" && state.layout === "layered" && !state.open.length
        ? "Expand a cluster to see its statements and inference steps."
        : undefined,
  };
}

function emptyView(anchor: string | null, message: string): GraphViewModel {
  return { nodes: [], edges: [], anchor, statementCount: 0, frontierCount: 0, truncated: 0, message };
}
