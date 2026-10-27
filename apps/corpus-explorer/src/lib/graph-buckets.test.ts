import { describe, expect, test } from "bun:test";
import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

import { areaOfNamespace, laneOfNamespace, NO_LEAN_AREA, parseAreas } from "./graph-areas";
import { bucketCanMatch, mergeBuckets, planBuckets, type GraphBucket } from "./graph-bucket-view";
import { buildGraphBuckets, type GraphBuckets } from "./graph-buckets";
import { closureOf } from "./graph-facets";
import { DEFAULT_STATE, parseGraphState, serializeGraphState, type GraphState } from "./graph-state";
import { computeGraphView, indexGraph } from "./graph-view";
import { fixtureGraph } from "./frontier-fixture";
import { getGraphBuckets } from "./graph-bucket-data";
import { fixture } from "./proposition-graph.fixture";

const repository = fileURLToPath(new URL("../../../../", import.meta.url));
const state = (query: string): GraphState => parseGraphState(new URLSearchParams(query));

describe("areas and lanes", () => {
  test("areas come from scripts/root_imports.py and match its area_of", () => {
    const areas = parseAreas(readFileSync(`${repository}scripts/root_imports.py`, "utf8"));
    expect(areas).toContain("Greek/NewTestament");
    const namespaces = [
      "TruthCore.Greek.NewTestament.Mark",
      "TruthCore.Greek.Aristotle.Physics",
      "TruthCore.Results.Case.Catholicism.StageThree.X",
      "TruthCore.Results.Aquinas",
      "TruthCore.Modal",
    ];
    const python = JSON.parse(execFileSync("python3", ["-c", `
import json, sys
from pathlib import Path
sys.path.insert(0, 'scripts')
from root_imports import area_of
print(json.dumps([area_of(Path('/'.join(name.split('.')[1:]) + '/M.lean')) for name in json.loads(sys.argv[1])]))
`, JSON.stringify(namespaces)], { cwd: repository, encoding: "utf8" }));
    expect(namespaces.map((namespace) => areaOfNamespace(namespace, areas))).toEqual(python);
    expect(areaOfNamespace(undefined, areas)).toBe(NO_LEAN_AREA);
  });

  test("lanes follow AGENTS.md: lane B inside lane A and C directories", () => {
    expect(laneOfNamespace("TruthCore.Latin.Aquinas.SummaTheologiae")).toBe("A");
    expect(laneOfNamespace("TruthCore.Case.Catholicism")).toBe("A");
    expect(laneOfNamespace("TruthCore.Case.Catholicism.StageThree.Miracles")).toBe("B");
    expect(laneOfNamespace("TruthCore.Comparison.Resurrection")).toBe("B");
    expect(laneOfNamespace("TruthCore.Comparison.Metaethics")).toBe("C");
    expect(laneOfNamespace(undefined)).toBe("none");
  });
});

function checkPartition({ manifest, buckets, lookup }: GraphBuckets, statements: number, inferences: number) {
  const owner = new Map<string, string>();
  for (const bucket of buckets) {
    for (const record of [...bucket.statements, ...bucket.inferences]) {
      expect(owner.has(record.id)).toBe(false);
      owner.set(record.id, bucket.id);
    }
    expect(bucket.nodes.length).toBe(bucket.statements.length + bucket.inferences.length);
  }
  expect(owner.size).toBe(statements + inferences);
  // No inference step or research link crosses a bucket boundary.
  for (const bucket of buckets) {
    for (const inference of bucket.inferences) {
      for (const id of [...inference.inputs, ...inference.assumptions, inference.output]) expect(owner.get(id)).toBe(bucket.id);
    }
    for (const relation of bucket.relations) {
      if (relation.subject === relation.object) continue;
      expect(owner.get(relation.subject)).toBe(bucket.id);
      expect(owner.get(relation.object)).toBe(bucket.id);
    }
  }
  for (const [id, index] of lookup) {
    if (owner.has(id)) expect(manifest.buckets[index].id).toBe(owner.get(id)!);
  }
  for (const [index, summary] of manifest.buckets.entries()) {
    expect(summary.id).toBe(buckets[index].id);
    const counted = Object.values(summary.facets.closure).reduce((sum, count) => sum + count, 0);
    expect(counted).toBe(summary.statements);
  }
  return owner;
}

describe("graph buckets", () => {
  test("fixture: whole components per bucket, root bucket holds every root-reaching statement", () => {
    const graph = fixtureGraph(fixture);
    const built = buildGraphBuckets(graph);
    const owner = checkPartition(built, graph.statements.length, graph.inferences.length);
    expect(built.manifest.defaultBuckets).toEqual(["root"]);
    for (const statement of graph.statements.filter((entry) => entry.reachesRoot)) expect(owner.get(statement.id)).toBe("root");
    expect(owner.get("LONE")).not.toBe("root");
  });

  test("real corpus: partition, facet totals and the default view", () => {
    const built = getGraphBuckets();
    const owner = checkPartition(built, built.graph.statements.length, built.graph.inferences.length);
    const reaching = built.graph.statements.filter((statement) => statement.reachesRoot);
    expect(reaching.length).toBeGreaterThan(0);
    for (const statement of reaching) expect(owner.get(statement.id)).toBe("root");
    const isolated = built.manifest.buckets.filter((bucket) => bucket.kind === "isolated");
    expect(isolated.every((bucket) => bucket.inferences === 0)).toBe(true);
    const root = built.manifest.buckets.find((bucket) => bucket.id === "root")!;
    expect(root.statements).toBeLessThan(built.graph.statements.length / 2);
    const frontier = built.graph.statements.filter((statement) => statement.frontier).length;
    expect(built.manifest.buckets.reduce((sum, bucket) => sum + bucket.frontier, 0)).toBe(frontier);
  });
});

describe("bucket plans", () => {
  // SOLO is a singleton: no inference and no research link.
  const graph = fixtureGraph({ ...fixture, statements: [...fixture.statements, { id: "SOLO", paraphrase: "Solo reading.", lean_declaration: "TruthCore.Other.SOLO" }] });
  const built = buildGraphBuckets(graph);
  const { manifest, lookup, search } = built;
  const byId = new Map(built.buckets.map((bucket) => [bucket.id, bucket]));
  const owner = (id: string) => built.buckets.find((bucket) => bucket.statements.some((statement) => statement.id === id))?.id;

  test("default overview loads the root bucket only; singletons load when shown", () => {
    expect(planBuckets(manifest, DEFAULT_STATE, null, null)).toEqual({ wanted: ["root"], needsLookup: false, needsSearch: false });
    const shown = planBuckets(manifest, state("islands=1"), null, null).wanted;
    expect(shown).toContain("root");
    expect(shown.some((id) => id.startsWith("isolated-"))).toBe(true);
    expect(planBuckets(manifest, state("b=all"), null, null).wanted.some((id) => id.startsWith("isolated-"))).toBe(false);
  });

  test("facet filters skip buckets without a possible match", () => {
    const plan = planBuckets(manifest, state("closure=established"), null, null).wanted;
    for (const id of manifest.buckets.map((bucket) => bucket.id)) {
      const bucket = byId.get(id) as GraphBucket;
      const matches = bucket.statements.some((statement) => closureOf(statement) === "established");
      // The default bucket stays as dimmed context.
      expect(plan.includes(id)).toBe(matches || manifest.defaultBuckets.includes(id));
    }
    expect(planBuckets(manifest, state("b=root&closure=established"), null, null).wanted).toEqual(["root"]);
    expect(manifest.buckets.every((bucket) => bucketCanMatch(bucket, DEFAULT_STATE))).toBe(true);
  });

  test("addressed IDs and text queries wait for their index, then load their buckets", () => {
    const target = graph.statements.find((statement) => !statement.reachesRoot && statement.id !== "LONE")!;
    const addressed = state(`view=focus&node=${target.id}`);
    expect(planBuckets(manifest, addressed, null, null)).toEqual({ wanted: [], needsLookup: true, needsSearch: false });
    const resolved = planBuckets(manifest, addressed, lookup, null);
    expect(resolved.wanted).toHaveLength(1);
    expect(byId.get(resolved.wanted[0])!.statements.some((statement) => statement.id === target.id)).toBe(true);
    const query = planBuckets(manifest, state("q=solo"), null, search);
    expect(query.needsSearch).toBe(true);
    expect(query.wanted).toEqual(["root", owner("SOLO")]);
  });

  test("merged buckets reproduce the views of the whole graph", () => {
    const merged = mergeBuckets(manifest, built.buckets);
    expect(merged.graph.statements.length).toBe(graph.statements.length);
    expect(merged.network.positions.size).toBe(graph.statements.length + graph.inferences.length);
    const index = indexGraph(merged.graph);
    for (const query of ["view=root", "view=focus&node=C&hops=2", "view=local&node=C&hops=2", "view=all&islands=1"]) {
      const view = (input: typeof graph) => computeGraphView(input, state(query), indexGraph(input));
      const ids = (input: typeof graph) => view(input).nodes.map((node) => node.id).sort();
      expect(ids(merged.graph)).toEqual(ids(graph));
    }
    expect(index.statementById.size).toBe(graph.statements.length);
    // Bucket boxes never overlap after shelf packing.
    const boxes = built.buckets.map((bucket) => {
      const points = bucket.nodes.map(([id]) => merged.network.positions.get(id)!);
      return { minX: Math.min(...points.map((p) => p.x)), maxX: Math.max(...points.map((p) => p.x)), minY: Math.min(...points.map((p) => p.y)), maxY: Math.max(...points.map((p) => p.y)) };
    });
    for (const [i, left] of boxes.entries()) {
      for (const right of boxes.slice(i + 1)) {
        const overlap = left.minX <= right.maxX && right.minX <= left.maxX && left.minY <= right.maxY && right.minY <= left.maxY;
        expect(overlap).toBe(false);
      }
    }
  });
});

test("facet filters and bucket selection round-trip through the URL", () => {
  const query = "area=Greek%2FNewTestament&area=Latin&lane=B&closure=frontier-bare&rec=claim&rec=result&reach=root&b=root&b=linked-latin-1";
  const parsed = state(query);
  expect(parsed.area).toEqual(["Greek/NewTestament", "Latin"]);
  expect(parsed.reach).toBe("root");
  expect(serializeGraphState(parsed)).toBe(query);
  expect(state("closure=bogus&rec=nope&reach=sideways")).toEqual(DEFAULT_STATE);
});
