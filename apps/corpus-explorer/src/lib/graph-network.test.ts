import { expect, test } from "bun:test";
import { fixtureGraph } from "./frontier-fixture";
import { fixture } from "./proposition-graph.fixture";
import { networkStructure, NETWORK_TICKS } from "./graph-network";
import { computeGraphView } from "./graph-view";
import { DEFAULT_STATE, parseGraphState, serializeGraphState } from "./graph-state";
import { getPropositionGraph } from "./proposition-graph-data";

const graph = fixtureGraph(fixture);

test("network keeps AND junctions, shared statements, components and distinct leaves", () => {
  const structure = networkStructure(graph);
  expect(structure.degree.get("I1")).toBe(3);
  expect(structure.unsupported.has("P1")).toBe(true);
  expect(structure.unsupported.has("C")).toBe(false);
  expect(structure.unconsumed.has("ROOT")).toBe(true);
  expect(structure.unconsumed.has("P1")).toBe(false);
  expect(structure.positions.size).toBe(graph.statements.length + graph.inferences.length);
  expect(structure.components.flat().length).toBe(structure.positions.size);
  const view = computeGraphView(graph, DEFAULT_STATE);
  expect(view.nodes.filter((node) => node.id === "P1")).toHaveLength(1);
  expect(view.edges.filter((edge) => edge.target === "I1")).toHaveLength(2);
  expect(view.edges.filter((edge) => edge.kind === "relation")).toHaveLength(4);
  for (const edge of view.edges) {
    if (edge.kind === "relation") continue;
    expect(graph.inferences.some((step) => step.id === edge.source || step.id === edge.target)).toBe(true);
  }
});

test("layout is deterministic under input permutation; research proximity never changes proof connectivity", () => {
  const original = networkStructure(graph);
  const reordered = networkStructure({ ...graph, statements: [...graph.statements].reverse(), inferences: [...graph.inferences].reverse(), relations: [...graph.relations].reverse() });
  expect([...reordered.positions]).toEqual([...original.positions]);
  expect([...reordered.community]).toEqual([...original.community]);
  const inferenceOnly = networkStructure({ ...graph, relations: [] });
  expect(inferenceOnly.positions).not.toEqual(original.positions);
  expect(inferenceOnly.components).toEqual(original.components);
  expect(original.layoutComponentCount).toBeLessThan(original.components.length);
  expect(inferenceOnly.layoutComponentCount).toBe(inferenceOnly.components.length);
  expect(inferenceOnly.degree).toEqual(original.degree);
  expect(inferenceOnly.unsupported).toEqual(original.unsupported);
  expect(inferenceOnly.unconsumed).toEqual(original.unconsumed);
});

test("cycles and reciprocal inferences retain directed edges without circular closure", () => {
  const cycle = { ...graph, inferences: [...graph.inferences, { ...graph.inferences[0], id: "BACK", inputs: ["C"], output: "P1" }] };
  expect(networkStructure(cycle).unsupported.has("P1")).toBe(false);
  const view = computeGraphView(cycle, DEFAULT_STATE);
  expect(view.edges.some((edge) => edge.source === "BACK" && edge.target === "P1")).toBe(true);
  expect(cycle.statements.find((node) => node.id === "P1")?.established).toBe(false);
});

test("network/leaf/overlay filters round-trip and never show partial premises", () => {
  const state = { ...DEFAULT_STATE, layout: "layered" as const, leaf: "unsupported" as const, relations: true, q: "P1", hide: true };
  expect(parseGraphState(new URLSearchParams(serializeGraphState(state)))).toEqual(state);
  const view = computeGraphView(graph, { ...state, layout: "network" });
  expect(view.nodes.some((node) => node.id === "P1")).toBe(true);
  expect(view.nodes.some((node) => node.id === "I1")).toBe(false);
});

test("frontier emphasis is shareable presentation state, not a different proof graph", () => {
  const allState = { ...DEFAULT_STATE, emphasis: "all" as const };
  expect(parseGraphState(new URLSearchParams(serializeGraphState(allState)))).toEqual(allState);
  const normal = computeGraphView(graph, DEFAULT_STATE);
  const emphasized = computeGraphView(graph, allState);
  expect(emphasized.nodes).toEqual(normal.nodes);
  expect(emphasized.edges).toEqual(normal.edges);
});

test("global frontier keeps research-linked readings but suppresses otherwise unlinked readings", () => {
  const connected = computeGraphView(graph, { ...DEFAULT_STATE, relations: false });
  const all = computeGraphView(graph, { ...DEFAULT_STATE, relations: false, showIsolated: true });
  expect(connected.nodes.length).toBeLessThan(all.nodes.length);
  expect(connected.edges).toEqual(all.edges);
  expect(computeGraphView(graph, DEFAULT_STATE).nodes.some((node) => node.id === "LONE")).toBe(true);
  expect(connected.nodes.filter((node) => node.kind === "statement" && node.statement.frontier)).toEqual(
    all.nodes.filter((node) => node.kind === "statement" && node.statement.frontier),
  );
  const state = { ...DEFAULT_STATE, showIsolated: true };
  expect(parseGraphState(new URLSearchParams(serializeGraphState(state)))).toEqual(state);
});

test("selected and expanded disconnected readings remain visible in the global frontier", () => {
  const selection = { ...DEFAULT_STATE, relations: false, sel: "LONE", expanded: ["LONE"] };
  const restored = parseGraphState(new URLSearchParams(serializeGraphState(selection)));
  expect(restored).toEqual(selection);
  expect(computeGraphView(graph, { ...DEFAULT_STATE, relations: false }).nodes.some((node) => node.id === "LONE")).toBe(false);
  const view = computeGraphView(graph, restored);
  expect(view.nodes.some((node) => node.id === "LONE")).toBe(true);
  expect(view.edges).toEqual(computeGraphView(graph, { ...DEFAULT_STATE, relations: false }).edges);
  const filtered = computeGraphView(graph, { ...restored, q: "no-other-statement-matches", hide: true });
  expect(filtered.nodes.some((node) => node.id === "LONE")).toBe(true);
});

test("real corpus: bounded settled layout for 1000+ statements", () => {
  const corpus = getPropositionGraph();
  expect(corpus.statements.length).toBeGreaterThan(1000);
  const start = performance.now();
  const structure = networkStructure(corpus);
  console.info(JSON.stringify({ workload: "real-corpus-network", statements: corpus.statements.length, inferences: corpus.inferences.length, ticks: NETWORK_TICKS, components: structure.components.length, layoutMs: Math.round(performance.now() - start) }));
  expect(structure.positions.size).toBe(corpus.statements.length + corpus.inferences.length);
  expect([...structure.positions.values()].every((point) => Number.isFinite(point.x) && Number.isFinite(point.y))).toBe(true);
}, 30000);
