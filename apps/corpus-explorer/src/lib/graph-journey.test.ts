import { expect, test } from "bun:test";

import { DEFAULT_STATE, parseGraphState, serializeGraphState } from "./graph-state";
import { inspectDispute, restoreOverview, restoreSupport, traceSupport } from "./graph-journey";

test("network → one-hop AND/OR support → dispute → support → original network", () => {
  const overview = {
    ...DEFAULT_STATE,
    sel: "P",
    obligation: "OPEN-P",
    viewport: "126,-32,0.7654",
    q: "reason",
    closure: ["frontier-supported" as const],
    expanded: ["Q"],
    layout: "network" as const,
  };
  const support = traceSupport(overview, "P");
  expect(support).toMatchObject({
    view: "focus", layout: "layered", node: "P", sel: "P", dir: "down", hops: 1,
    viewport: "", returnView: serializeGraphState(overview),
  });
  const deeper = { ...support, hops: 3 };
  const dispute = inspectDispute(deeper, "Q");
  expect(dispute).toMatchObject({ view: "dispute", node: "Q", sel: "Q", layout: "network", viewport: "" });
  expect(parseGraphState(new URLSearchParams(dispute.supportView))).toMatchObject({
    view: "focus", node: "P", sel: "P", hops: 3, dir: "down",
  });

  const shared = parseGraphState(new URLSearchParams(serializeGraphState(dispute)));
  expect(restoreSupport(shared)).toEqual(deeper);
  expect(restoreOverview(shared)).toEqual(overview);
  expect(restoreOverview(restoreSupport(shared))).toEqual(overview);
});

test("direct dispute retains a return path without inventing a support history", () => {
  const overview = { ...DEFAULT_STATE, sel: "P", relations: false, area: ["Metaphysics"] };
  const dispute = inspectDispute(overview, "P");
  expect(dispute.supportView).toBe("");
  expect(restoreSupport(dispute)).toBeNull();
  expect(restoreOverview(dispute)).toEqual(overview);
});

test("invalid support snapshots cannot masquerade as a previous proof view", () => {
  expect(restoreSupport({ ...DEFAULT_STATE, supportView: "view=dispute&node=P" })).toBeNull();
  expect(restoreSupport(DEFAULT_STATE)).toBeNull();
});
