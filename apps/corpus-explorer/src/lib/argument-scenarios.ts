import type { ForestTreeModel } from "./argument-forest";

export type AssumptionScenario = {
  /** Explicit user selections, not Truth Core's established-statement set. */
  accepted: ReadonlySet<string>;
  denied: ReadonlySet<string>;
  /** Accepted statements plus consequences reachable through recorded result-bearing arguments. */
  reachable: ReadonlySet<string>;
  /** Newly reached conclusions and every applicable recorded argument route. */
  derived: ReadonlyMap<string, readonly string[]>;
  /** Denied conclusions reached from accepted premises, without propagating through the conflict. */
  conflicts: ReadonlyMap<string, readonly string[]>;
};

/**
 * A local hypothetical AND/OR walk, not the corpus's frontier-closure algorithm
 * and not a new verdict about truth or proof. Only arguments with recorded
 * results and ordinary premises participate; bare research relationships and
 * zero-premise results with undisplayed commitments cannot silently fire.
 */
export function exploreAssumptions(
  model: ForestTreeModel,
  acceptedIds: Iterable<string>,
  deniedIds: Iterable<string>,
): AssumptionScenario {
  const accepted = new Set([...acceptedIds].filter((id) => Boolean(model.statements[id])));
  const denied = new Set([...deniedIds].filter((id) => Boolean(model.statements[id]) && !accepted.has(id)));
  const reachable = new Set(accepted);
  const derived = new Map<string, string[]>();
  const conflicts = new Map<string, string[]>();
  const argumentsWithResults = Object.values(model.arguments)
    .filter((argument) => argument.resultIds.length > 0 && argument.premises.length > 0);

  let changed = true;
  while (changed) {
    changed = false;
    for (const argument of argumentsWithResults) {
      if (!argument.premises.every((id) => reachable.has(id))) { continue; }
      const target = denied.has(argument.conclusion) ? conflicts : derived;
      if (!accepted.has(argument.conclusion) || denied.has(argument.conclusion)) {
        const routes = target.get(argument.conclusion) ?? [];
        if (!routes.includes(argument.id)) {
          routes.push(argument.id);
          target.set(argument.conclusion, routes);
        }
      }
      if (!denied.has(argument.conclusion) && !reachable.has(argument.conclusion)) {
        reachable.add(argument.conclusion);
        changed = true;
      }
    }
  }
  return { accepted, denied, reachable, derived, conflicts };
}
