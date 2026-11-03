/** Explicit personal selections only. Corpus closure and verified status live elsewhere. */
export type BeliefProfile = { accepted: string[]; denied: string[] };

export const BELIEF_STORAGE_KEY = "truth-core:belief-profile:v1";
export const EMPTY_BELIEFS: BeliefProfile = { accepted: [], denied: [] };

function uniqueKnown(value: unknown, known: ReadonlySet<string>): string[] {
  if (!Array.isArray(value)) { return []; }
  return [...new Set(value.filter((id): id is string => typeof id === "string" && known.has(id)))].sort();
}

/** Local storage is untrusted input: reject old schemas, unknown IDs and overlapping selections. */
export function readBeliefProfile(raw: string | null, known: ReadonlySet<string>): BeliefProfile {
  if (!raw) { return EMPTY_BELIEFS; }
  try {
    const value: unknown = JSON.parse(raw);
    if (!value || typeof value !== "object" || Array.isArray(value) ||
      !("version" in value) || value.version !== 1) { return EMPTY_BELIEFS; }
    const accepted = uniqueKnown("accepted" in value ? value.accepted : null, known);
    const selected = new Set(accepted);
    const denied = uniqueKnown("denied" in value ? value.denied : null, known).filter((id) => !selected.has(id));
    return { accepted, denied };
  } catch {
    return EMPTY_BELIEFS;
  }
}

export function writeBeliefProfile(profile: BeliefProfile): string {
  return JSON.stringify({ version: 1, accepted: [...profile.accepted].sort(), denied: [...profile.denied].sort() });
}

export function chooseBelief(profile: BeliefProfile, id: string, value: "true" | "false" | "clear"): BeliefProfile {
  const accepted = new Set(profile.accepted);
  const denied = new Set(profile.denied);
  accepted.delete(id);
  denied.delete(id);
  if (value === "true") { accepted.add(id); }
  if (value === "false") { denied.add(id); }
  return { accepted: [...accepted].sort(), denied: [...denied].sort() };
}

export function rejectBeliefs(profile: BeliefProfile, ids: readonly string[]): BeliefProfile {
  const rejected = new Set(ids);
  return { accepted: profile.accepted.filter((id) => !rejected.has(id)), denied: profile.denied };
}
