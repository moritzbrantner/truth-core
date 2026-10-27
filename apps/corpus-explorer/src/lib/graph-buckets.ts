/**
 * Build-time partition of the /graph data into static JSON buckets (#491).
 *
 * Partition: layout components (inference steps plus recorded research links,
 * graph-network.ts) are never split. The components that contain a statement
 * reaching the root (`reaching_root_statements` of `corpus.py frontier`) form
 * the default `root` bucket. Other linked components are grouped by their most
 * frequent import area and chunked; isolated readings (singleton components)
 * are grouped by area separately, so hiding singletons skips those files.
 * Each bucket carries its own precomputed network layout and facet counts.
 */
import { createHash } from "node:crypto";

import type { BucketFacets, BucketKind, BucketNode, BucketSummary, FacetCounts, GraphBucket, GraphLookup, GraphManifest, GraphSearchIndex } from "./graph-bucket-view";
import { areaOf, closureOf, laneOf, reachOf, recordKindsOf } from "./graph-facets";
import { networkStructure } from "./graph-network";
import { indexGraph } from "./graph-view";
import type { PropositionGraph } from "./proposition-graph";

export const MAX_LINKED_BUCKET_NODES = 600;
export const MAX_ISOLATED_BUCKET_STATEMENTS = 300;
const BUCKET_MARGIN = 40;

export type GraphBuckets = { manifest: GraphManifest; buckets: GraphBucket[]; lookup: GraphLookup; search: GraphSearchIndex };

const slug = (text: string) => text.toLowerCase().replace(/[^a-z0-9]+/g, "-").replace(/^-|-$/g, "") || "none";

function count(counts: FacetCounts, key: string) {
  counts[key] = (counts[key] ?? 0) + 1;
}

export function buildGraphBuckets(graph: PropositionGraph): GraphBuckets {
  const index = indexGraph(graph);
  const whole = networkStructure(graph);
  const reaching = new Set(graph.statements.filter((statement) => statement.reachesRoot).map((statement) => statement.id));
  const anchor = graph.defaultTarget;

  const componentArea = (component: string[]) => {
    const counts = new Map<string, number>();
    for (const id of component) {
      const statement = index.statementById.get(id);
      if (statement) counts.set(areaOf(statement), (counts.get(areaOf(statement)) ?? 0) + 1);
    }
    return [...counts].sort((left, right) => right[1] - left[1] || left[0].localeCompare(right[0]))[0]?.[0] ?? "(none)";
  };

  type Group = { id: string; label: string; kind: BucketKind; area: string; components: string[][] };
  const groups: Group[] = [];
  const root: string[][] = [];
  const linked = new Map<string, string[][]>();
  const isolated = new Map<string, string[][]>();
  for (const component of whole.layoutComponents) {
    if (component.some((id) => reaching.has(id) || id === anchor)) {
      root.push(component);
      continue;
    }
    const target = component.length === 1 ? isolated : linked;
    const area = componentArea(component);
    target.set(area, [...(target.get(area) ?? []), component]);
  }
  if (root.length) {
    groups.push({ id: "root", label: `Paths into ${anchor ?? "the root"}`, kind: "root", area: componentArea(root.flat()), components: root });
  }
  const chunked = (source: Map<string, string[][]>, kind: BucketKind, limit: number) => {
    for (const [area, components] of [...source].sort(([left], [right]) => left.localeCompare(right))) {
      const chunks: string[][][] = [];
      let size = Infinity;
      for (const component of components) {
        if (size + component.length > limit) {
          chunks.push([]);
          size = 0;
        }
        chunks[chunks.length - 1].push(component);
        size += component.length;
      }
      chunks.forEach((chunk, number) => {
        const suffix = chunks.length > 1 ? ` (${number + 1}/${chunks.length})` : "";
        groups.push({
          id: `${kind}-${slug(area)}-${number + 1}`,
          label: `${kind === "isolated" ? "Unlinked readings" : "Linked components"} · ${area}${suffix}`,
          kind,
          area,
          components: chunk,
        });
      });
    }
  };
  chunked(linked, "linked", MAX_LINKED_BUCKET_NODES);
  chunked(isolated, "isolated", MAX_ISOLATED_BUCKET_STATEMENTS);

  const bucketOf = new Map<string, number>();
  groups.forEach((group, number) => group.components.flat().forEach((id) => bucketOf.set(id, number)));

  const buckets: GraphBucket[] = [];
  const summaries: BucketSummary[] = [];
  for (const group of groups) {
    const ids = new Set(group.components.flat());
    const subgraph: PropositionGraph = {
      ...graph,
      statements: graph.statements.filter((statement) => ids.has(statement.id)),
      inferences: graph.inferences.filter((inference) => ids.has(inference.id)),
      arguments: graph.arguments.filter((argument) => [argument.conclusion, ...argument.premises].some((id) => ids.has(id))),
      relations: graph.relations.filter((relation) => ids.has(relation.subject) || ids.has(relation.object)),
    };
    const network = networkStructure(subgraph);
    const points = [...network.positions.values()];
    const minX = Math.min(0, ...points.map((point) => point.x));
    const minY = Math.min(0, ...points.map((point) => point.y));
    const nodes: BucketNode[] = [...network.positions].map(([id, point]) => [
      id,
      Math.round((point.x - minX) * 10) / 10,
      Math.round((point.y - minY) * 10) / 10,
      network.community.get(id) ?? 0,
      network.degree.get(id) ?? 0,
    ]);
    const facets: BucketFacets = { area: {}, lane: {}, closure: {}, rec: {}, reach: {}, status: {}, source: {} };
    for (const statement of subgraph.statements) {
      count(facets.area, areaOf(statement));
      count(facets.lane, laneOf(statement));
      count(facets.closure, closureOf(statement));
      count(facets.reach, reachOf(statement));
      count(facets.status, statement.status);
      for (const kind of recordKindsOf(statement, index)) count(facets.rec, kind);
      for (const source of statement.sourceIds) count(facets.source, source);
    }
    buckets.push({
      id: group.id,
      statements: subgraph.statements,
      inferences: subgraph.inferences,
      arguments: subgraph.arguments,
      relations: subgraph.relations,
      nodes,
      components: network.components.length,
      layoutComponents: network.layoutComponentCount,
    });
    summaries.push({
      id: group.id,
      label: group.label,
      kind: group.kind,
      area: group.area,
      statements: subgraph.statements.length,
      inferences: subgraph.inferences.length,
      frontier: subgraph.statements.filter((statement) => statement.frontier).length,
      width: Math.ceil(Math.max(0, ...nodes.map((node) => node[1]))) + BUCKET_MARGIN,
      height: Math.ceil(Math.max(0, ...nodes.map((node) => node[2]))) + BUCKET_MARGIN,
      facets,
    });
  }

  const bucketIds = groups.map((group) => group.id);
  const located = <T extends { id: string }>(records: T[], locate: (record: T) => string | undefined) =>
    records.flatMap((record): Array<[string, number]> => {
      const at = locate(record);
      const bucket = at === undefined ? undefined : bucketOf.get(at);
      return bucket === undefined ? [] : [[record.id, bucket]];
    });
  const lookup: GraphLookup = [
    ...located(graph.statements, (statement) => statement.id),
    ...located(graph.inferences, (inference) => inference.id),
    ...located(graph.arguments, (argument) => argument.conclusion),
  ];
  const search: GraphSearchIndex = graph.statements.flatMap((statement): GraphSearchIndex => {
    const bucket = bucketOf.get(statement.id);
    return bucket === undefined ? [] : [[statement.id, bucket, statement.paraphrase, statement.leanDeclaration ?? ""]];
  });
  return {
    buckets,
    lookup,
    search,
    manifest: {
      version: createHash("sha256").update(JSON.stringify([summaries, buckets, lookup, search])).digest("hex").slice(0, 12),
      buckets: summaries,
      defaultBuckets: root.length ? ["root"] : bucketIds.slice(0, 1),
      sources: graph.sources,
      defaultTarget: graph.defaultTarget,
      rootPresent: graph.rootPresent,
      totals: {
        statements: graph.statements.length,
        inferences: graph.inferences.length,
        components: whole.components.length,
        layoutComponents: whole.layoutComponentCount,
        relations: graph.relations.length,
      },
    },
  };
}
