export type ProofSearchState = {
  explore: boolean;
  proofBudget: number;
  proofScope: string[];
};

export const DEFAULT_PROOF_BUDGET = 1500;

export function parseProofSearchState(params: Pick<URLSearchParams, "get" | "getAll">): ProofSearchState {
  const budget = Number(params.get("proofBudget") ?? DEFAULT_PROOF_BUDGET);
  return {
    explore: params.get("explore") === "1",
    proofBudget: Number.isFinite(budget) ? Math.max(1, Math.min(10000, Math.floor(budget))) : DEFAULT_PROOF_BUDGET,
    proofScope: [...new Set(params.getAll("proofScope").filter(Boolean))].sort(),
  };
}

export function appendProofSearchState(params: URLSearchParams, state: ProofSearchState) {
  if (state.explore) {
    params.set("explore", "1");
  }
  if (state.proofBudget !== DEFAULT_PROOF_BUDGET) {
    params.set("proofBudget", String(state.proofBudget));
  }
  for (const id of [...new Set(state.proofScope)].sort()) {
    params.append("proofScope", id);
  }
}
