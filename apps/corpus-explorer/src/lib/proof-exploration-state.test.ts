import { expect, test } from "bun:test";
import { appendProofSearchState, parseProofSearchState } from "./proof-exploration-state";

test("proof overlays, deterministic budget and established scope round-trip in URL", () => {
  const state = { explore: true, proofBudget: 700, proofScope: ["A", "B"] };
  const params = new URLSearchParams();
  appendProofSearchState(params, state);
  expect(parseProofSearchState(params)).toEqual(state);
  expect(parseProofSearchState(new URLSearchParams("proofBudget=Infinity" )).proofBudget).toBe(1500);
  expect(parseProofSearchState(new URLSearchParams("proofBudget=-7&proofScope=A&proofScope=A"))).toEqual({ explore: false, proofBudget: 1, proofScope: ["A"] });
});
