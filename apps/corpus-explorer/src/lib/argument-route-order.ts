import type { ForestArgument } from "./argument-forest";
import type { AssumptionScenario } from "./argument-scenarios";

export type RouteOrder = "beliefs" | "shortest" | "recorded";
export type RouteReadiness = "reached" | "needs" | "blocked" | "unlisted";

export type RankedRoute = {
  argument: ForestArgument;
  readiness: RouteReadiness;
  /** Distinct ordinary premises reached by explicit choice or recorded result. */
  reachedCount: number;
  totalCount: number;
  missing: string[];
  denied: string[];
};

const readinessRank: Record<RouteReadiness, number> = {
  reached: 0,
  needs: 1,
  blocked: 2,
  unlisted: 3,
};

function resultRank(argument: ForestArgument): number {
  if (!argument.resultIds.length) { return 2; }
  return argument.transcriptionOnly ? 1 : 0;
}

/**
 * Rank recorded OR alternatives for navigation, never as probabilities or proofs.
 * In particular, zero-premise records cannot fire in a hypothetical scenario:
 * the corpus may have commitments not represented by ordinary premises.
 */
export function orderArgumentRoutes(
  argumentsForConclusion: readonly ForestArgument[],
  scenario: AssumptionScenario,
  order: RouteOrder = "beliefs",
): RankedRoute[] {
  const routes = argumentsForConclusion.map((argument) => {
    const premises = [...new Set(argument.premises)];
    const denied = premises.filter((id) => scenario.denied.has(id));
    const missing = premises.filter((id) => !scenario.denied.has(id) && !scenario.reachable.has(id));
    const readiness: RouteReadiness = !premises.length ? "unlisted"
      : denied.length ? "blocked"
        : missing.length ? "needs" : "reached";
    return {
      argument,
      readiness,
      reachedCount: premises.length - denied.length - missing.length,
      totalCount: premises.length,
      missing,
      denied,
    };
  });

  if (order === "recorded") { return routes; }
  return routes.sort((left, right) => {
    if (order === "shortest") {
      // Unknown hidden conditions never become the shortest-looking proof.
      return Number(left.readiness === "unlisted") - Number(right.readiness === "unlisted") ||
        left.totalCount - right.totalCount ||
        resultRank(left.argument) - resultRank(right.argument) ||
        left.argument.id.localeCompare(right.argument.id);
    }
    return readinessRank[left.readiness] - readinessRank[right.readiness] ||
      left.denied.length - right.denied.length ||
      left.missing.length - right.missing.length ||
      resultRank(left.argument) - resultRank(right.argument) ||
      left.totalCount - right.totalCount ||
      left.argument.id.localeCompare(right.argument.id);
  });
}
