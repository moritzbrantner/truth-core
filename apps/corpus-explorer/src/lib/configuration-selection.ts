import type { AssumptionNode, VerifiedConfigurationCase } from "./verified-configurations";

type Terminal = Extract<AssumptionNode, { kind: "terminal" }>;

/** Follow the canonical Python decision tree; no browser-side classification. */
export function selectedConfiguration(
  space: VerifiedConfigurationCase["assumption_space"],
  selected: readonly string[],
): { terminal: Terminal; error?: never } | { error: string; terminal?: never } {
  const chosen = new Set(selected);
  if (chosen.size !== selected.length || selected.some((id) => !space.statement_ids.includes(id))) {
    return { error: "This selection contains unsupported or repeated statement IDs." };
  }
  const nodes = new Map(space.nodes.map((node) => [node.id, node]));
  let current = space.root;
  for (let step = 0; step <= space.nodes.length; step += 1) {
    const node = nodes.get(current);
    if (!node) { return { error: "The configuration report contains a broken decision path." }; }
    if (node.kind === "terminal") {
      const allowed = new Set([...node.required_statement_ids, ...node.optional_statement_ids]);
      if (node.required_statement_ids.some((id) => !chosen.has(id)) || selected.some((id) => !allowed.has(id))) {
        return { error: "This selection is outside the certified assumption family." };
      }
      return { terminal: node };
    }
    current = chosen.has(node.statement_id) ? node.include : node.exclude;
  }
  return { error: "The configuration report contains a circular decision path." };
}
