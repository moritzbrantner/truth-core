import type { RegisteredConfigurationCase } from "./configuration-cases";
import type { VerifiedConfigurationCase } from "./verified-configurations";

/** Trust only the existing verified transport, never registrations or attempt metadata. */
export function comparisonOutcomes(entry: RegisteredConfigurationCase | VerifiedConfigurationCase) {
  return entry.configurations.map((cell) => ({
    id: cell.id,
    status: entry.verified ? cell.status : "verification required",
    premises: cell.statement_ids,
  }));
}

export function senseCellOutcome() {
  // No canonical sense × rival mapping exists. A certificate cannot be guessed from labels.
  return "Untested: no explicit sense × rival certificate mapping.";
}

/** An annotation describes its owning certificate; it never establishes the target. */
export function certificateOutcome(outcome: "excluded" | "model-witnessed" | "unresolved" | "untested" | undefined, transcription: boolean) {
  if (outcome === undefined) return senseCellOutcome();
  if (transcription) return "unresolved: owning result is a transcription";
  return ({ excluded: "checked exclusion under recorded conditions", "model-witnessed": "model-witnessed compatibility under recorded conditions", unresolved: "unresolved", untested: "untested" })[outcome];
}
