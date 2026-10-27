import type { FloorBasis, FloorDisagreement } from "./site-state";

/**
 * Display text for floor markings (#500). Whether a criterion holds is read
 * from `floor` of `corpus.py frontier --json`; nothing here evaluates it.
 * Client-safe: no Node imports.
 */

/** The floor basis criteria (docs/decisions/2026-10-27-01-floor-basis-criteria.md). */
export const FLOOR_BASIS_DESCRIPTIONS: Record<FloorBasis, string> = {
  retorsion: "A verified derivation refutes the recorded denial from closed premises only.",
  common_ground: "No recorded rival, and every position on the disputed question has a proponent claim stating it.",
  observation: "A claim states it, and every recorded rival is a refuted global sceptical position.",
  legacy: "Documented legacy marking without a basis; closure is reported relative to it.",
};

/** Recorded disagreement as text: the rivals and claims, or "none recorded". */
export function describeDisagreement(disagreement: FloorDisagreement) {
  if (disagreement === null) return "not recorded (the positions' agreement is the record)";
  if (disagreement === "none recorded") return "none recorded";
  return [
    ...(disagreement.rival_statement_ids?.length ? [`rivals ${disagreement.rival_statement_ids.join(", ")}`] : []),
    ...(disagreement.claim_ids?.length ? [`claims ${disagreement.claim_ids.join(", ")}`] : []),
  ].join("; ");
}
