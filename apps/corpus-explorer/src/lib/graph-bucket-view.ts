/**
 * Client side of the bucketed /graph data (#491): bucket types, which buckets a
 * view needs, and how loaded buckets merge into one proposition graph.
 *
 * A bucket is a union of whole layout components (inference steps plus
 * recorded research links, as in graph-network.ts). No inference, argument path
 * or research link crosses buckets, so a root-path, focus or local view around
 * a node is complete once that node's bucket is loaded.
 */
import type { Point } from "./graph-layout";
import { hasFilters, type GraphState } from "./graph-state";
import type { CorpusSourceInput, GraphArgument, GraphInference, GraphRelation, GraphStatement, PropositionGraph } from "./proposition-graph";

export type BucketKind = "root" | "linked" | "isolated";
export type FacetCounts = Record<string, number>;
export type BucketFacets = {
  area: FacetCounts;
  lane: FacetCounts;
  closure: FacetCounts;
  rec: FacetCounts;
  reach: FacetCounts;
  status: FacetCounts;
  source: FacetCounts;
};

export type BucketSummary = {
  id: string;
  label: string;
  kind: BucketKind;
  /** Most frequent statement area in the bucket. */
  area: string;
  statements: number;
  inferences: number;
  frontier: number;
  width: number;
  height: number;
  facets: BucketFacets;
};

export type GraphManifest = {
  /** Content hash of every bucket file; part of each fetch URL. */
  version: string;
  buckets: BucketSummary[];
  /** Buckets of the default overview: the components reaching the root. */
  defaultBuckets: string[];
  sources: CorpusSourceInput[];
  defaultTarget: string | null;
  rootPresent: boolean;
  totals: { statements: number; inferences: number; components: number; layoutComponents: number; relations: number };
};

/** [id, x, y, community, degree], positions relative to the bucket's own box. */
export type BucketNode = [string, number, number, number, number];

export type GraphBucket = {
  id: string;
  statements: GraphStatement[];
  inferences: GraphInference[];
  arguments: GraphArgument[];
  relations: GraphRelation[];
  nodes: BucketNode[];
  /** Inference-only components inside the bucket. */
  components: number;
  layoutComponents: number;
};

/** Lazily fetched: [statement, inference or argument ID, index into `manifest.buckets`]. */
export type GraphLookup = Array<[string, number]>;
/** Lazily fetched for text queries: [statement ID, bucket index, paraphrase, Lean declaration]. */
export type GraphSearchIndex = Array<[string, number, string, string]>;

export type LoadedNetwork = {
  positions: Map<string, Point>;
  community: Map<string, number>;
  degree: Map<string, number>;
  unsupported: Set<string>;
  unconsumed: Set<string>;
  researchLinked: Set<string>;
  componentCount: number;
  layoutComponentCount: number;
};

export const ALL_BUCKETS = "all";
export const BUCKET_GAP = 80;

export const bucketPath = (basePath: string, file: string, version: string) =>
  `${basePath}/graph-data/${file}.json?v=${version}`;

/** IDs the URL addresses directly; their buckets load whatever the filters say. */
export function referencedIds(state: GraphState, defaultTarget: string | null) {
  const ids = [state.sel, state.node, state.target, state.arg, ...state.pins, ...state.expanded];
  if ((state.view === "root" || state.explore) && !state.target && defaultTarget) ids.push(defaultTarget);
  // Proof exploration searches from its target and scope seeds; their buckets must be loaded.
  if (state.explore) ids.push(...state.proofScope);
  return [...new Set(ids.filter(Boolean))];
}

/** Every selected value of every active facet occurs in the bucket. */
export function bucketCanMatch(bucket: BucketSummary, state: GraphState) {
  const any = (counts: FacetCounts, values: readonly string[]) => values.some((value) => (counts[value] ?? 0) > 0);
  if (state.area.length && !any(bucket.facets.area, state.area)) return false;
  if (state.lane.length && !any(bucket.facets.lane, state.lane)) return false;
  if (state.closure.length && !any(bucket.facets.closure, state.closure)) return false;
  if (state.rec.length && !any(bucket.facets.rec, state.rec)) return false;
  if (state.reach && !any(bucket.facets.reach, [state.reach])) return false;
  if (state.status.length && !any(bucket.facets.status, state.status)) return false;
  if (state.source && !any(bucket.facets.source, [state.source])) return false;
  if (state.leaf === "frontier" && !any(bucket.facets.closure, ["frontier-bare", "frontier-sourced"])) return false;
  return true;
}

export type BucketPlan = {
  /** Buckets to show, in manifest order. */
  wanted: string[];
  /** The lookup (addressed IDs) or search index (text query) is needed before the plan is complete. */
  needsLookup: boolean;
  needsSearch: boolean;
};

/**
 * Which buckets a view shows. The overview shows the explicit `b` selection,
 * otherwise the default (root) buckets plus, when filters are active, every
 * other bucket that can match: facet filters skip buckets with no possible
 * match, a text query keeps only buckets with a matching statement, and
 * isolated readings stay unloaded unless shown or filtered for. Root-path,
 * focus and local views need only the buckets of the nodes they are built
 * around; any addressed node's bucket is always added.
 */
export function planBuckets(
  manifest: GraphManifest,
  state: GraphState,
  lookup: GraphLookup | null,
  search: GraphSearchIndex | null,
): BucketPlan {
  const query = state.q.trim().toLowerCase();
  const references = referencedIds(state, manifest.defaultTarget);
  const known = new Set(manifest.buckets.map((bucket) => bucket.id));
  const wanted = new Set<string>();
  if (state.view === "all") {
    const explicit = state.buckets.filter((id) => id === ALL_BUCKETS || known.has(id));
    const everything = explicit.includes(ALL_BUCKETS) || (!explicit.length && hasFilters(state));
    // Filters reach matching unlinked readings, as before bucketing.
    const showIsolated = state.showIsolated || state.layout === "layered" || hasFilters(state);
    const base = new Set(
      everything
        ? manifest.buckets.map((bucket) => bucket.id)
        : explicit.length
          ? explicit
          : [
            ...manifest.defaultBuckets,
            // Showing singletons in the default overview loads every singleton bucket.
            ...(state.showIsolated ? manifest.buckets.filter((bucket) => bucket.kind === "isolated").map((bucket) => bucket.id) : []),
          ],
    );
    const textBuckets = query && search ? textMatchBuckets(manifest, search, query) : null;
    // Without an explicit selection the default buckets stay as dimmed context.
    const kept = new Set(explicit.length ? [] : manifest.defaultBuckets);
    for (const bucket of manifest.buckets) {
      if (!base.has(bucket.id)) continue;
      if (kept.has(bucket.id)) {
        wanted.add(bucket.id);
        continue;
      }
      if (bucket.kind === "isolated" && !showIsolated && !explicit.includes(bucket.id)) continue;
      if (!bucketCanMatch(bucket, state)) continue;
      if (query && (!textBuckets || !textBuckets.has(bucket.id))) continue;
      wanted.add(bucket.id);
    }
  }
  if (lookup) {
    const location = lookupLocations(lookup);
    for (const id of references) {
      const bucket = manifest.buckets[location.get(id) ?? -1];
      if (bucket) wanted.add(bucket.id);
    }
  }
  return {
    wanted: manifest.buckets.map((bucket) => bucket.id).filter((id) => wanted.has(id)),
    needsLookup: references.length > 0,
    needsSearch: Boolean(query) && state.view === "all",
  };
}

const locationCache = new WeakMap<GraphLookup, Map<string, number>>();
export function lookupLocations(lookup: GraphLookup) {
  let location = locationCache.get(lookup);
  if (!location) {
    location = new Map(lookup);
    locationCache.set(lookup, location);
  }
  return location;
}

/** Same text test as `statementMatches` (ID, paraphrase, Lean declaration). */
export function textMatchBuckets(manifest: GraphManifest, search: GraphSearchIndex, query: string) {
  const buckets = new Set<string>();
  const needle = query.trim().toLowerCase();
  for (const [id, bucket, paraphrase, lean] of search) {
    if ([id, paraphrase, lean].some((text) => text.toLowerCase().includes(needle))) {
      const summary = manifest.buckets[bucket];
      if (summary) buckets.add(summary.id);
    }
  }
  return buckets;
}

/**
 * One proposition graph and network from the loaded buckets. Bucket boxes are
 * packed into shelves in manifest order, so a bucket keeps its internal layout
 * and the overview never re-runs a force simulation in the browser.
 */
export function mergeBuckets(manifest: GraphManifest, buckets: GraphBucket[]): { graph: PropositionGraph; network: LoadedNetwork } {
  const summaries = new Map(manifest.buckets.map((bucket) => [bucket.id, bucket]));
  const order = new Map(manifest.buckets.map((bucket, index) => [bucket.id, index]));
  const sorted = [...buckets].sort((left, right) => (order.get(left.id) ?? 0) - (order.get(right.id) ?? 0));
  const positions = new Map<string, Point>();
  const community = new Map<string, number>();
  const degree = new Map<string, number>();
  const shelfWidth = Math.max(1600, ...sorted.map((bucket) => summaries.get(bucket.id)?.width ?? 0));
  let shelfX = 0;
  let shelfY = 0;
  let shelfHeight = 0;
  let communityOffset = 0;
  const statements: GraphStatement[] = [];
  const inferences: GraphInference[] = [];
  const argumentById = new Map<string, GraphArgument>();
  const relationById = new Map<string, GraphRelation>();
  let componentCount = 0;
  let layoutComponentCount = 0;
  for (const bucket of sorted) {
    const summary = summaries.get(bucket.id);
    const width = summary?.width ?? 0;
    const height = summary?.height ?? 0;
    if (shelfX && shelfX + width > shelfWidth) {
      shelfX = 0;
      shelfY += shelfHeight + BUCKET_GAP;
      shelfHeight = 0;
    }
    let maxCommunity = -1;
    for (const [id, x, y, group, links] of bucket.nodes) {
      positions.set(id, { x: x + shelfX, y: y + shelfY });
      community.set(id, group + communityOffset);
      degree.set(id, links);
      maxCommunity = Math.max(maxCommunity, group);
    }
    communityOffset += maxCommunity + 1;
    shelfX += width + BUCKET_GAP;
    shelfHeight = Math.max(shelfHeight, height);
    statements.push(...bucket.statements);
    inferences.push(...bucket.inferences);
    for (const argument of bucket.arguments) argumentById.set(argument.id, argument);
    for (const relation of bucket.relations) relationById.set(relation.id, relation);
    componentCount += bucket.components;
    layoutComponentCount += bucket.layoutComponents;
  }
  const graph: PropositionGraph = {
    statements,
    inferences,
    arguments: [...argumentById.values()].sort((left, right) => left.id.localeCompare(right.id)),
    relations: [...relationById.values()].sort((left, right) => left.id.localeCompare(right.id)),
    sources: manifest.sources,
    defaultTarget: manifest.defaultTarget,
    rootPresent: manifest.rootPresent,
  };
  const produced = new Set(inferences.map((inference) => inference.output));
  const consumed = new Set(inferences.flatMap((inference) => [...inference.inputs, ...inference.assumptions]));
  const researchLinked = new Set<string>();
  for (const relation of graph.relations) {
    if (relation.subject === relation.object) continue;
    researchLinked.add(relation.subject);
    researchLinked.add(relation.object);
  }
  return {
    graph,
    network: {
      positions,
      community,
      degree,
      unsupported: new Set(statements.filter((statement) => !produced.has(statement.id)).map((statement) => statement.id)),
      unconsumed: new Set(statements.filter((statement) => !consumed.has(statement.id)).map((statement) => statement.id)),
      researchLinked,
      componentCount,
      layoutComponentCount,
    },
  };
}
