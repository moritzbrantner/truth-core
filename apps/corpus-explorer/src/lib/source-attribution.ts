import type { FrontierItem } from "./site-state";

/** Describe recorded relationships, not the fidelity or truth of a claim. */
export function sourceAttribution(item: Pick<FrontierItem, "stating_claims" | "supporting_claims">): string {
  if (item.stating_claims.length) {
    return item.supporting_claims.length
      ? "Source claims directly attribute this statement, and source claims are also linked as support."
      : "Source claims directly attribute this statement.";
  }
  if (item.supporting_claims.length) {
    return "No source claim directly attributes this statement. Related source claims are linked as support, but do not necessarily state the full proposition.";
  }
  return "It is bare: no source claim directly attributes it and no source claim is linked as support.";
}
