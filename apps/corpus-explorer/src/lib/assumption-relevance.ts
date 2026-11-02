import type { ForestTreeModel } from "./argument-forest";
import type { AssumptionScenario } from "./argument-scenarios";

export type RouteReadiness = {
  /** A result record and ordinary premises are both required for scenario propagation. */
  applicable: boolean;
  transcriptionOnly: boolean;
  satisfied: number;
  contradicted: number;
  unresolved: number;
  /** Unresolved propositions that themselves have recorded result routes. */
  unresolvedWithSupport: number;
};

export type AssumptionRelevance = {
  /** Shortest number of recorded AND/OR support edges back to the focused goal. */
  goalDistance: ReadonlyMap<string, number>;
  /** Number of distinct result-bearing argument routes consuming the proposition. */
  downstreamRoutes: ReadonlyMap<string, number>;
  /** A single unresolved ordinary premise of a result route on the goal's support path. */
  completesGoalRoute: ReadonlySet<string>;
  routeReadiness: ReadonlyMap<string, RouteReadiness>;
};

/**
 * Read-only relevance over the existing forest. Distances include research-only
 * argument records for navigation, never as implied truths. Traversal is
 * iterative so cyclic and heavily shared subgraphs do not grow a call stack.
 */
export function buildAssumptionRelevance(
  model: ForestTreeModel,
  goal: string,
  scenario: AssumptionScenario,
): AssumptionRelevance {
  const argumentsByConclusion = new Map<string, string[]>();
  const downstreamRoutes = new Map<string, number>();
  const routeReadiness = new Map<string, RouteReadiness>();
  for (const argument of Object.values(model.arguments)) {
    const forConclusion = argumentsByConclusion.get(argument.conclusion) ?? [];
    forConclusion.push(argument.id);
    argumentsByConclusion.set(argument.conclusion, forConclusion);
    const premises = new Set(argument.premises);
    let satisfied = 0;
    let contradicted = 0;
    let unresolved = 0;
    let unresolvedWithSupport = 0;
    for (const premise of premises) {
      if (scenario.denied.has(premise)) { contradicted += 1; }
      else if (scenario.reachable.has(premise)) { satisfied += 1; }
      else {
        unresolved += 1;
        if (model.statements[premise]?.argumentIds.some((id) =>
          model.arguments[id]?.resultIds.length && model.arguments[id].premises.length)) {
          unresolvedWithSupport += 1;
        }
      }
      if (argument.resultIds.length && model.statements[premise]) {
        downstreamRoutes.set(premise, (downstreamRoutes.get(premise) ?? 0) + 1);
      }
    }
    routeReadiness.set(argument.id, {
      applicable: argument.resultIds.length > 0 && premises.size > 0,
      transcriptionOnly: argument.transcriptionOnly,
      satisfied, contradicted, unresolved, unresolvedWithSupport,
    });
  }

  const goalDistance = new Map<string, number>();
  if (model.statements[goal]) {
    goalDistance.set(goal, 0);
    const queue = [goal];
    for (let cursor = 0; cursor < queue.length; cursor += 1) {
      const id = queue[cursor];
      const distance = goalDistance.get(id)!;
      for (const argumentId of argumentsByConclusion.get(id) ?? []) {
        for (const premise of model.arguments[argumentId].premises) {
          if (!model.statements[premise] || goalDistance.has(premise)) { continue; }
          goalDistance.set(premise, distance + 1);
          queue.push(premise);
        }
      }
    }
  }

  const completesGoalRoute = new Set<string>();
  for (const argument of Object.values(model.arguments)) {
    const readiness = routeReadiness.get(argument.id)!;
    if (!readiness.applicable || readiness.contradicted || readiness.unresolved !== 1 ||
      !goalDistance.has(argument.conclusion) || scenario.reachable.has(argument.conclusion) ||
      scenario.denied.has(argument.conclusion)) { continue; }
    for (const premise of argument.premises) {
      if (!scenario.reachable.has(premise) && !scenario.denied.has(premise) && model.statements[premise]) {
        completesGoalRoute.add(premise);
      }
    }
  }
  return { goalDistance, downstreamRoutes, completesGoalRoute, routeReadiness };
}

/** Ready result routes first, then the closest unblocked paths; denied premises last. */
export function sortAssumptionArguments(
  ids: readonly string[], relevance: AssumptionRelevance,
): string[] {
  const readiness = (id: string): RouteReadiness => relevance.routeReadiness.get(id) ?? {
    applicable: false, transcriptionOnly: false, satisfied: 0, contradicted: 0, unresolved: 0, unresolvedWithSupport: 0,
  };
  const lane = (route: RouteReadiness) => {
    if (route.contradicted) { return 4; }
    if (!route.applicable) { return 3; }
    if (route.unresolved) { return 2; }
    return route.transcriptionOnly ? 1 : 0;
  };
  return [...ids].sort((left, right) => {
    const a = readiness(left);
    const b = readiness(right);
    return lane(a) - lane(b) ||
      a.contradicted - b.contradicted ||
      a.unresolved - b.unresolved ||
      Number(a.transcriptionOnly) - Number(b.transcriptionOnly) ||
      b.unresolvedWithSupport - a.unresolvedWithSupport ||
      b.satisfied - a.satisfied ||
      left.localeCompare(right);
  });
}

function matchQuality(id: string, paraphrase: string, query: string): number | null {
  const statementId = id.toLowerCase();
  const title = paraphrase.toLowerCase();
  if (statementId === query) { return 0; }
  if (statementId.startsWith(query)) { return 1; }
  if (title === query) { return 2; }
  if (title.startsWith(query)) { return 3; }
  if (title.includes(query)) { return 4; }
  if (statementId.includes(query)) { return 5; }
  const tokens = query.split(/\s+/).filter(Boolean);
  if (tokens.length > 1 && tokens.every((token) => title.includes(token))) { return 6; }
  if (tokens.length > 1 && tokens.every((token) => title.includes(token) || statementId.includes(token))) { return 7; }
  return null;
}

function goalDistance(relevance: AssumptionRelevance, id: string): number {
  return relevance.goalDistance.get(id) ?? Infinity;
}

/** Exact/textual matches remain authoritative; the active goal and profile break ties. */
export function rankPropositionMatches(
  model: ForestTreeModel,
  rawQuery: string,
  relevance: AssumptionRelevance,
  scenario: AssumptionScenario,
  limit = 24,
): ForestTreeModel["statements"][string][] {
  const query = rawQuery.trim().toLowerCase();
  if (!query || limit <= 0) { return []; }
  const matches = Object.values(model.statements).flatMap((entry) => {
    const quality = matchQuality(entry.id, entry.paraphrase, query);
    return quality === null ? [] : [{ entry, quality }];
  });
  matches.sort((left, right) => {
    const a = left.entry.id;
    const b = right.entry.id;
    const active = (id: string) => Number(scenario.accepted.has(id) || scenario.denied.has(id) || scenario.derived.has(id));
    const resultCount = (id: string) => model.statements[id].argumentIds
      .filter((argumentId) => model.arguments[argumentId]?.resultIds.length).length;
    return left.quality - right.quality ||
      Number(relevance.completesGoalRoute.has(b)) - Number(relevance.completesGoalRoute.has(a)) ||
      goalDistance(relevance, a) - goalDistance(relevance, b) ||
      active(b) - active(a) ||
      resultCount(b) - resultCount(a) ||
      (relevance.downstreamRoutes.get(b) ?? 0) - (relevance.downstreamRoutes.get(a) ?? 0) ||
      a.localeCompare(b);
  });
  return matches.slice(0, limit).map(({ entry }) => entry);
}

/** A display order only: the source scenario's reachable and certified sets stay unchanged. */
export function rankImplications(
  derived: ReadonlyMap<string, readonly string[]>,
  relevance: AssumptionRelevance,
): Array<[string, readonly string[]]> {
  return [...derived.entries()].sort(([a, routesA], [b, routesB]) =>
    goalDistance(relevance, a) - goalDistance(relevance, b) ||
    (relevance.downstreamRoutes.get(b) ?? 0) - (relevance.downstreamRoutes.get(a) ?? 0) ||
    routesB.length - routesA.length ||
    a.localeCompare(b));
}
