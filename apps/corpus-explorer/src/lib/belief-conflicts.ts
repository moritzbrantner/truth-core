/** A producer-verified incompatible conjunction within one named semantic profile. */
export type CertifiedBeliefCore = {
  key: string;
  caseId: string;
  /** Display labels of the case and results; ids stay opaque. */
  caseLabel?: string;
  resultLabels?: Record<string, string>;
  profile: string;
  statementIds: string[];
  resultIds: string[];
};

export type BeliefConflictReview = {
  cores: CertifiedBeliefCore[];
  /** Inclusion-minimal old-belief sets whose removal hits every displayed core. */
  repairs: string[][];
  truncated: boolean;
  cannotRepairByRejectingOldBeliefs: boolean;
};

/** Membership in a certified core is exact; a research rivalry is not a conflict. */
export function activeCertifiedCores(
  accepted: ReadonlySet<string>,
  cores: readonly CertifiedBeliefCore[],
): CertifiedBeliefCore[] {
  return cores.filter((core) => core.statementIds.every((id) => accepted.has(id)));
}

function subset(left: readonly string[], right: readonly string[]): boolean {
  return left.every((id) => right.includes(id));
}

function minimal(sets: string[][]): string[][] {
  const unique = new Map(sets.map((set) => {
    const sorted = [...new Set(set)].sort();
    return [sorted.join("|"), sorted];
  }));
  const ordered = [...unique.values()].sort((a, b) => a.length - b.length || a.join("|").localeCompare(b.join("|")));
  return ordered.filter((candidate, index) => !ordered.slice(0, index).some((other) => subset(other, candidate)));
}

/**
 * Recommend deletions, not logical consequences. Each option removes at least
 * one *previously accepted* member of every newly activated certified core.
 * Removing displayed cores does not certify the remaining configuration.
 */
export function reviewNewBelief(
  priorAccepted: ReadonlySet<string>,
  proposedId: string,
  certifiedCores: readonly CertifiedBeliefCore[],
  maxOptions = 128,
): BeliefConflictReview {
  const next = new Set([...priorAccepted, proposedId]);
  const cores = activeCertifiedCores(next, certifiedCores).filter((core) => core.statementIds.includes(proposedId));
  if (!cores.length) { return { cores: [], repairs: [], truncated: false, cannotRepairByRejectingOldBeliefs: false }; }
  const constraints = cores.map((core) => core.statementIds.filter((id) => id !== proposedId && priorAccepted.has(id)));
  if (constraints.some((ids) => !ids.length)) {
    return { cores, repairs: [], truncated: false, cannotRepairByRejectingOldBeliefs: true };
  }
  let repairs: string[][] = [[]];
  let truncated = false;
  for (const constraint of constraints) {
    repairs = minimal(repairs.flatMap((current) =>
      constraint.some((id) => current.includes(id)) ? [current] : constraint.map((id) => [...current, id])));
    if (repairs.length > maxOptions) {
      repairs = repairs.slice(0, maxOptions);
      truncated = true;
    }
  }
  return { cores, repairs, truncated, cannotRepairByRejectingOldBeliefs: false };
}
