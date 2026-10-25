import { expect, test } from "bun:test";
import { fixture } from "./proposition-graph.fixture";
import { fixtureGraph } from "./frontier-fixture";
import { runProofExploration } from "./proof-exploration";
import { proofOverlay } from "./proof-overlay";

test("overlays retain target, established forward, required backward and blockers separately", () => {
  const graph = fixtureGraph(fixture);
  const result = runProofExploration(graph, { target: "ROOT", budget: 1500 });
  const overlay = proofOverlay(graph, result);
  expect(overlay.get("ROOT")?.target).toBe(true);
  expect(overlay.get("SE")?.established).toBe(true);
  expect(overlay.get("SE")?.junction).toBe(true);
  expect(overlay.get("P1")?.blocker).toBe(true);
  expect(overlay.get("P1")?.forward).toBe(false);
  expect(overlay.get("I1")?.backward).toBe(true);
  expect(proofOverlay(graph, null).size).toBe(0);
});
