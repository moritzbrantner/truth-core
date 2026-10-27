"use client";

import {
  Controls,
  Handle,
  MarkerType,
  Position,
  ReactFlow,
  useStore,
  useReactFlow,
  type Edge,
  type NodeChange,
  type Node,
  type NodeProps,
} from "@xyflow/react";
import Link from "next/link";
import { ResearchQueue } from "./research-queue";
import { orderObligations, type ResearchObligation } from "@/lib/research-frontier";
import { usePathname, useRouter, useSearchParams } from "next/navigation";
import { useEffect, useMemo, useRef, useState } from "react";

import { ALL_BUCKETS, type GraphManifest, type LoadedNetwork } from "@/lib/graph-bucket-view";
import { CLOSURE_FACETS, RECORD_FACETS, REACH_FACETS } from "@/lib/graph-facets";
import { LANES } from "@/lib/graph-areas";
import { useGraphBuckets } from "./use-graph-buckets";
import { NetworkMarker } from "./network-marker";
import { layeredLayout } from "@/lib/graph-layout";
import {
  MAX_HOPS,
  hasFilters,
  parseGraphState,
  parseViewport,
  serializeGraphState,
  type GraphState,
} from "@/lib/graph-state";
import {
  computeGraphView,
  indexGraph,
  searchStatements,
  type ViewClusterNode,
  type ViewEdge,
  type ViewInferenceNode,
  type ViewNode,
  type ViewStatementNode,
} from "@/lib/graph-view";
import {
  GRAPH_STATUSES,
  type GraphStatement,
  type GraphStatus,
  type PropositionGraph,
} from "@/lib/proposition-graph";

import { ProofExplorationControls } from "./proof-exploration-controls";
import { ProofExplorationPanel } from "./proof-exploration-panel";
import { useProofExploration } from "./use-proof-exploration";
import { lemmaResearchObligation } from "@/lib/proof-exploration";
import { describeDisagreement } from "@/lib/floor";
import { proofOverlay, type ProofOverlay } from "@/lib/proof-overlay";
import proofStyles from "./proof-overlay.module.css";

const statusLabel = new Map(GRAPH_STATUSES.map((status) => [status.id, status.label]));

const NODE_SIZE = {
  statement: { width: 280, height: 132 },
  inference: { width: 190, height: 46 },
  cluster: { width: 250, height: 104 },
} as const;

type FlowData = { view: ViewNode; selected: boolean; proof?: ProofOverlay } & Record<string, unknown>;
type FlowNode = Node<FlowData>;

function StatementNodeView({ data }: NodeProps<FlowNode>) {
  const node = data.view as ViewStatementNode;
  const statement = node.statement;
  const provenance = statement.claims.slice(0, 2);
  return (
    <div
      className="graph-node graph-node-statement"
      data-proof-target={data.proof?.target ?? false}
      data-proof-forward={data.proof?.forward ?? false}
      data-proof-backward={data.proof?.backward ?? false}
      data-proof-junction={data.proof?.junction ?? false}
      data-proof-blocker={data.proof?.blocker ?? false}
      data-anchor={node.anchor}
      data-dimmed={!node.matched}
      data-frontier={statement.frontier}
      data-highlighted={node.highlighted}
      data-selected={data.selected}
      data-status={statement.status}
    >
      <Handle position={Position.Bottom} type="target" />
      <div className="graph-node-button">
        <span className="graph-node-status">
          {statement.established
            ? "Established"
            : statement.closureReason
              ? "Closed · conditional"
              : statusLabel.get(statement.status)}
          {statement.refuted ? " · refuted" : ""}
          {statement.frontier
            ? ` · frontier (${statement.frontierDepth}) · ${statement.transitiveDependentArguments} dependent`
            : ""}
        </span>
        {data.proof?.forward || data.proof?.backward ? <span className="graph-node-status">{data.proof?.established ? "Forward established" : data.proof?.forward ? "Forward proposed" : "Backward required"}{data.proof?.junction ? " · proposed junction" : ""}{data.proof?.blocker ? " · branch blocker" : ""}</span> : null}
        <span className="graph-node-text">{statement.paraphrase}</span>
        <span className="graph-node-badges">
          {provenance.map((claim) => (
            <span className="graph-badge" key={claim.id} title={`${claim.id}: ${claim.locator}`}>
              {claim.sourceId}
              {claim.reading ? ` · ${claim.reading}` : ""}
            </span>
          ))}
          {statement.claims.length > provenance.length ? (
            <span className="graph-badge">+{statement.claims.length - provenance.length}</span>
          ) : null}
          {statement.stages.map((stage) => (
            <span className="graph-badge" key={stage}>
              stage {stage}
            </span>
          ))}
        </span>
      </div>
      <Handle position={Position.Top} type="source" />
    </div>
  );
}

function InferenceNodeView({ data }: NodeProps<FlowNode>) {
  const node = data.view as ViewInferenceNode;
  return (
    <div
      className="graph-node graph-node-inference"
      data-proof-target={data.proof?.target ?? false}
      data-proof-forward={data.proof?.forward ?? false}
      data-proof-backward={data.proof?.backward ?? false}
      data-proof-junction={data.proof?.junction ?? false}
      data-proof-blocker={data.proof?.blocker ?? false}
      data-anchor={node.anchor}
      data-dimmed={!node.matched}
      data-highlighted={node.highlighted}
      data-selected={data.selected}
    >
      <Handle position={Position.Bottom} type="target" />
      <div className="graph-node-button" title={node.inference.meaning}>
        <span aria-hidden="true">⊢ </span>
        {node.inference.rule.replaceAll("_", " ")}
      </div>
      <Handle position={Position.Top} type="source" />
    </div>
  );
}

function ClusterNodeView({ data }: NodeProps<FlowNode>) {
  const node = data.view as ViewClusterNode;
  return (
    <div className="graph-node graph-node-cluster" data-dimmed={node.matchCount === 0}>
      <Handle position={Position.Bottom} type="target" />
      <div className="graph-node-button">
        <span className="graph-node-status">Cluster · click to expand</span>
        <span className="graph-node-text">{node.label}</span>
        <span className="graph-node-badges">
          <span className="graph-badge">{node.size} statements</span>
          {node.matchCount !== node.size ? <span className="graph-badge">{node.matchCount} match</span> : null}
          {node.frontierCount ? <span className="graph-badge">{node.frontierCount} frontier</span> : null}
        </span>
      </div>
      <Handle position={Position.Top} type="source" />
    </div>
  );
}

const nodeTypes = {
  marker: NetworkMarker,
  statement: StatementNodeView,
  inference: InferenceNodeView,
  cluster: ClusterNodeView,
};

const edgeStyle: Record<ViewEdge["kind"], React.CSSProperties> = {
  premise: { stroke: "var(--line-strong)" },
  assumption: { stroke: "var(--line-strong)", strokeDasharray: "2 4" },
  conclusion: { stroke: "var(--accent)" },
  relation: { stroke: "var(--status-alternative)", strokeDasharray: "7 5" },
  cluster: { stroke: "var(--line-strong)", strokeDasharray: "1 5" },
};

function nodeDescription(node: ViewNode) {
  if (node.kind === "inference") { return `${node.id}: ${node.inference.meaning}`; }
  if (node.kind === "cluster") { return `${node.label}: ${node.size} statements`; }
  let status = String(node.statement.status);
  if (node.statement.frontier) { status = `${node.statement.frontierDepth} open frontier`; }
  return `${node.statement.paraphrase}; ${status}`;
}

const NO_MEASUREMENTS: ReadonlyMap<string, { width: number; height: number }> = new Map();

function hashIds(nodes: ViewNode[]) {
  let hash = 0;
  for (const node of nodes) {
    for (let index = 0; index < node.id.length; index += 1) {
      hash = (hash * 31 + node.id.charCodeAt(index)) | 0;
    }
  }
  return `${nodes.length}:${hash}`;
}

export function PropositionGraphExplorer({
  manifest,
  obligations,
}: {
  manifest: GraphManifest;
  obligations: ResearchObligation[];
}) {
  const pathname = usePathname();
  const router = useRouter();
  const searchParams = useSearchParams();
  const state = useMemo(() => parseGraphState(searchParams), [searchParams]);
  const buckets = useGraphBuckets(manifest, state);
  const { graph, network } = buckets;
  const index = useMemo(() => indexGraph(graph), [graph]);
  const compact = state.layout === "network" && (state.view === "all" || state.view === "local");
  // Hover emphasis is transient presentation state. It never changes the URL,
  // corpus relationships, or proof frontier.
  const [hoveredId, setHoveredId] = useState("");
  const view = useMemo(() => computeGraphView(graph, state, index), [graph, state, index]);
  const proofTarget = index.statementById.has(state.target) ? state.target : graph.defaultTarget ?? "";
  // Explore only once every bucket the view needs has loaded, so the search never
  // reports a result over a partial graph (#491).
  const proof = useProofExploration(graph, state.explore && !buckets.pending, { target: proofTarget, budget: state.proofBudget, scope: state.proofScope.length ? state.proofScope : undefined });
  const visibleProof = state.explore && proof.result?.target === proofTarget ? proof.result : null;
  const overlay = useMemo(() => proofOverlay(graph, visibleProof), [graph, visibleProof]);
  const lemmaObligation = useMemo(() => visibleProof ? lemmaResearchObligation(visibleProof, graph.defaultTarget ?? "") : null, [visibleProof, graph.defaultTarget]);
  const queue = useMemo(
    () =>
      orderObligations(lemmaObligation ? [...obligations, lemmaObligation] : obligations, {
        target: state.scope === "goal" ? state.target || graph.defaultTarget || "" : "",
        selected: state.sel,
        pins: state.pins,
        kind: state.kind,
      }),
    [obligations, lemmaObligation, graph.defaultTarget, state.scope, state.target, state.sel, state.pins, state.kind],
  );
  const activeObligation = queue.find((item) => item.id === state.obligation);
  const search = useMemo(() => searchStatements(graph, state, 12, index), [graph, state, index]);

  // Compose updates issued before the previous router.replace commits.
  const pendingState = useRef<GraphState | null>(null);
  useEffect(() => {
    pendingState.current = null;
  }, [searchParams]);
  // Array-valued fields take a function of the pending state so rapid clicks compose.
  const update = (patch: Partial<GraphState> | ((current: GraphState) => Partial<GraphState>)) => {
    const current = pendingState.current ?? state;
    const next = {
      ...current,
      ...(typeof patch === "function" ? patch(current) : patch),
    };
    pendingState.current = next;
    const query = serializeGraphState(next);
    router.replace(query ? `${pathname}?${query}` : pathname, {
      scroll: false,
    });
  };

  // Facet counts over the whole corpus, summed from the bucket manifest.
  const facetTotals = useMemo(() => {
    const totals: Record<"area" | "lane" | "closure" | "rec" | "reach", Record<string, number>> = { area: {}, lane: {}, closure: {}, rec: {}, reach: {} };
    for (const bucket of manifest.buckets) {
      for (const key of Object.keys(totals) as Array<keyof typeof totals>) {
        for (const [value, count] of Object.entries(bucket.facets[key])) totals[key][value] = (totals[key][value] ?? 0) + count;
      }
    }
    return totals;
  }, [manifest]);
  const isolatedCount = manifest.buckets.filter((bucket) => bucket.kind === "isolated").reduce((sum, bucket) => sum + bucket.statements, 0);
  const toggleFacet = (key: "area" | "lane" | "closure" | "rec", value: string) =>
    update((current) => {
      const values = current[key] as string[];
      return { [key]: values.includes(value) ? values.filter((entry) => entry !== value) : [...values, value], viewport: "" };
    });
  const toggleBucket = (id: string) =>
    update(() => {
      const next = buckets.wanted.includes(id) ? buckets.wanted.filter((entry) => entry !== id) : [...buckets.wanted, id];
      return { buckets: next, viewport: "" };
    });

  const tagOptions = useMemo(() => {
    const counts = new Map<string, number>();
    for (const statement of graph.statements) {
      for (const tag of statement.tags) counts.set(tag, (counts.get(tag) ?? 0) + 1);
    }
    const groups = new Map<string, Array<{ tag: string; count: number }>>();
    for (const [tag, count] of [...counts].sort(([left], [right]) => left.localeCompare(right))) {
      const group = tag.includes(":") ? tag.slice(0, tag.indexOf(":")) : "other";
      groups.set(group, [...(groups.get(group) ?? []), { tag, count }]);
    }
    return groups;
  }, [graph]);

  const flowKey = `${state.layout}:${state.view}:${view.anchor}:${state.cluster}:${hashIds(view.nodes)}`;
  // React Flow sizes, kept only for the canvas instance that measured them: a
  // remounted canvas measures its nodes and handles afresh.
  const [measurements, setMeasurements] = useState<{ key: string; sizes: ReadonlyMap<string, { width: number; height: number }> }>({ key: "", sizes: new Map() });
  const measured = measurements.key === flowKey ? measurements.sizes : NO_MEASUREMENTS;
  const { nodes, edges } = useMemo(() => {
    const hovered = compact && state.view === "local" && view.nodes.some((node) => node.id === hoveredId) ? hoveredId : "";
    const hoverNeighbors = new Set(hovered ? [hovered] : []);
    if (hovered) {
      for (const edge of view.edges) {
        if (edge.source === hovered) hoverNeighbors.add(edge.target);
        if (edge.target === hovered) hoverNeighbors.add(edge.source);
      }
    }
    const relatedIds = new Set(activeObligation?.statementIds ?? []);
    const frontierIds = new Set(graph.statements.filter((statement) => statement.frontier).map((statement) => statement.id));
    const frontierJunctions = new Set(graph.inferences.filter((inference) => [...inference.inputs, ...inference.assumptions].some((id) => frontierIds.has(id))).map((inference) => inference.id));
    const selectedSteps = index.inferenceById.has(state.sel)
      ? [index.inferenceById.get(state.sel)!]
      : [...(index.producers.get(state.sel) ?? []), ...(index.consumers.get(state.sel) ?? [])];
    for (const step of selectedSteps) {
      relatedIds.add(step.id);
      for (const id of [...step.inputs, ...step.assumptions, step.output]) { relatedIds.add(id); }
    }
    if (state.relations && state.sel) {
      for (const relation of graph.relations) {
        if (relation.subject === state.sel) relatedIds.add(relation.object);
        if (relation.object === state.sel) relatedIds.add(relation.subject);
      }
    }
    for (const argument of graph.arguments) {
      if (activeObligation?.recordIds.includes(argument.id)) {
        argument.inferenceIds.forEach((id) => relatedIds.add(id));
      }
    }
    const positions = compact ? network.positions : layeredLayout(
      view.nodes.map((node) => ({ id: node.id, ...NODE_SIZE[node.kind] })),
      view.edges.filter((edge) => edge.kind !== "relation"),
    );
    const flowNodes: FlowNode[] = view.nodes.map((node) => ({
      id: node.id,
      type: compact ? "marker" : node.kind,
      ariaLabel: nodeDescription(node),
      focusable: true,
      position: positions.get(node.id) ?? { x: 0, y: 0 },
      // Hand back React Flow's own measurement: a new node object without
      // `measured` is hidden until re-measured, which can race with overlay updates.
      measured: measured.get(`${compact ? "marker" : node.kind}:${node.id}`),
      // Dense research clusters can overlap. Keep the selected belief tappable
      // above its neighbours, especially in the mobile frontier inspector.
      zIndex: node.id === state.sel || node.id === hovered ? 20 : 0,
      data: {
        view: node.kind === "cluster" ? node : { ...node, highlighted: node.highlighted || relatedIds.has(node.id) },
        selected: node.id === state.sel || (state.view === "local" && node.id === view.anchor),
        hoverDimmed: Boolean(hovered) && !hoverNeighbors.has(node.id) && node.id !== state.sel,
        hoverNeighbor: Boolean(hovered) && hoverNeighbors.has(node.id),
        proof: overlay.get(node.id),
        community: network.community.get(node.id) ?? 0,
        degree: network.degree.get(node.id) ?? 0,
        emphasis: state.emphasis,
      },
      draggable: false,
      selectable: false,
      style: { width: compact ? 28 : NODE_SIZE[node.kind].width, height: compact ? 28 : undefined },
    }));
    const flowEdges: Edge[] = view.edges.map((edge) => {
      const research = edge.kind === "relation";
      const boundary = !research && (frontierIds.has(edge.source) || frontierIds.has(edge.target) || frontierJunctions.has(edge.source) || frontierJunctions.has(edge.target));
      const emphasized = compact && state.emphasis === "frontier";
      const highlighted = edge.highlighted || relatedIds.has(edge.source) || relatedIds.has(edge.target);
      const incident = hovered && (edge.source === hovered || edge.target === hovered);
      return {
        id: edge.id,
        source: edge.source,
        target: edge.target,
        type: compact || edge.kind === "relation" ? "straight" : "smoothstep",
        label: compact ? undefined : edge.label,
        style: {
          ...edgeStyle[edge.kind],
          stroke: emphasized && boundary ? "var(--status-open)" : edgeStyle[edge.kind].stroke,
          opacity: hovered ? (incident ? 1 : 0.08) : compact ? (research ? 0.55 : emphasized && !boundary ? 0.18 : 0.72) : 1,
          strokeWidth: incident || highlighted ? 2.5 : compact ? 1.1 : 1.25,
        },
        markerEnd: compact || edge.kind === "premise" || edge.kind === "assumption"
          ? undefined
          : { type: MarkerType.ArrowClosed, color: String(edgeStyle[edge.kind].stroke) },
      };
    });
    return { nodes: flowNodes, edges: flowEdges };
  }, [view, state.sel, state.emphasis, state.relations, state.view, hoveredId, activeObligation, graph.arguments, graph.statements, graph.inferences, graph.relations, compact, network, index, overlay, measured]);
  const onNodesChange = (changes: NodeChange<FlowNode>[]) => {
    const sizes = changes.flatMap((change) => (change.type === "dimensions" && change.dimensions ? [{ id: change.id, size: change.dimensions }] : []));
    if (!sizes.length) return;
    const types = new Map(nodes.map((node) => [node.id, node.type]));
    setMeasurements((current) => {
      const next = new Map(current.key === flowKey ? current.sizes : []);
      for (const { id, size } of sizes) next.set(`${types.get(id)}:${id}`, size);
      return { key: flowKey, sizes: next };
    });
  };

  const onNodeClick = (_event: unknown, node: FlowNode) => {
    const clicked = node.data.view;
    if (clicked.kind === "cluster") {
      update((current) => ({
        open: current.open.includes(clicked.key) ? current.open : [...current.open, clicked.key],
      }));
    } else {
      const obligation = queue.find((item) => item.statementIds.includes(clicked.id));
      update({ sel: clicked.id, obligation: obligation?.id ?? "" });
    }
  };

  const selectObligation = (item: ResearchObligation) => {
    const statement = index.statementById.get(item.statementIds[0]);
    update((current) => ({
      obligation: item.id,
      viewport: "",
      ...(statement
        ? {
            sel: statement.id,
            open: [...new Set([...current.open, statement.clusters[current.cluster]])],
            expanded: [...new Set([...current.expanded, statement.id])],
          }
        : {}),
    }));
  };
  const defaultTarget = graph.defaultTarget ?? "";
  const target = state.target || defaultTarget;
  const stageTargets = graph.stageConclusions.filter(({ statementId }) => index.statementById.has(statementId));

  return (
    <section aria-labelledby="graph-heading" className={proofStyles.overlay}>
      <datalist id="graph-statement-ids">
        {graph.statements.map((statement) => (
          <option key={statement.id} value={statement.id} />
        ))}
      </datalist>

      <div className="frontier-primary-controls">
        <div className="graph-segmented" role="group" aria-label="Graph scope">
          <button aria-pressed={state.scope === "global" && state.view === "all"} onClick={() => update({ scope: "global", view: "all", viewport: "" })} type="button">Global frontier</button>
          <button aria-pressed={state.scope === "goal" && state.view === "root"} onClick={() => update({ scope: "goal", view: "root", viewport: "", target: state.sel && index.statementById.has(state.sel) ? state.sel : target })} type="button">Selected goal frontier</button>
          <button aria-pressed={state.view === "local"} disabled={!index.statementById.has(state.sel) && !index.inferenceById.has(state.sel)} onClick={() => update({ view: "local", layout: "network", node: state.sel, scope: "global", viewport: "", returnView: state.returnView || serializeGraphState({ ...state, returnView: "" }) })} title="Select a proposition dot to explore its neighborhood" type="button">Local graph</button>
        </div>
        <div className="graph-segmented" role="group" aria-label="Layout">
          {(["network", "layered"] as const).map((layout) => <button key={layout} type="button" aria-pressed={state.layout === layout} onClick={() => update({ layout, viewport: "" })}>{layout === "network" ? "Network" : "Layered"}</button>)}
        </div>
        <label className="field-label frontier-search">Find a proposition
          <input className="field-control" onChange={(event) => update({ q: event.target.value })} placeholder="Search propositions or IDs" type="search" value={state.q} />
        </label>
        {state.view === "local" ? (
          <label className="field-label frontier-depth">Neighborhood depth
            <select className="field-control" value={state.hops} onChange={(event) => update({ hops: Number(event.target.value), viewport: "" })}>
              {Array.from({ length: MAX_HOPS + 1 }, (_, depth) => <option key={depth} value={depth}>{depth} {depth === 1 ? "hop" : "hops"}</option>)}
            </select>
          </label>
        ) : null}
        <button className="graph-button frontier-emphasis-button" type="button" aria-pressed={state.emphasis === "frontier"} onClick={() => update({ emphasis: state.emphasis === "frontier" ? "all" : "frontier" })}>
          {state.emphasis === "frontier" ? "Frontier highlighted" : "Show all equally"}
        </button>
        {state.returnView ? <button className="graph-button" type="button" onClick={() => update({ ...parseGraphState(new URLSearchParams(state.returnView)), returnView: "" })}>Return to overview</button> : null}
      </div>

      <details className="frontier-advanced">
        <summary>More views and filters</summary>
      <div className="graph-toolbar">
        <label className="graph-toggle">
          <input type="checkbox" checked={!state.showIsolated} onChange={(event) => update({ showIsolated: !event.target.checked, viewport: "" })} />
          Hide singletons: unlinked readings ({isolatedCount})
        </label>
        <label className="field-label">Structural / epistemic filter
          <select className="field-control" value={state.leaf} onChange={(event) => update({ leaf: event.target.value as GraphState["leaf"] })}>
            <option value="">All statements</option>
            <option value="unsupported">No supporting inference ({network.unsupported.size})</option>
            <option value="unconsumed">No dependent inference ({network.unconsumed.size})</option>
            <option value="frontier">Open frontier ({graph.statements.filter((node) => node.frontier).length})</option>
          </select>
        </label>
        <label className="graph-toggle"><input type="checkbox" checked={state.relations} onChange={(event) => update({ relations: event.target.checked })} />Recorded research links (not proof)</label>
        <div aria-label="View" className="graph-segmented" role="group">
          {(
            [
              ["root", "Root paths"],
              ["focus", "Focus"],
              ["local", "Local graph"],
              ["all", "Full graph"],
            ] as const
          ).map(([id, label]) => (
            <button
              aria-pressed={state.view === id}
              key={id}
              onClick={() =>
                update({
                  view: id,
                  ...((id === "focus" || id === "local") && state.view !== id
                    ? {
                        returnView: serializeGraphState({
                          ...state,
                          returnView: "",
                        }),
                        viewport: "",
                      }
                    : {}),
                })
              }
              type="button"
            >
              {label}
            </button>
          ))}
        </div>

        {state.view === "root" || state.scope === "goal" ? (
          <label className="field-label">
            Target statement
            <input
              className="field-control font-mono"
              list="graph-statement-ids"
              onChange={(event) =>
                update({
                  target: event.target.value === defaultTarget ? "" : event.target.value,
                })
              }
              placeholder={defaultTarget}
              value={state.target}
            />
          </label>
        ) : null}
        {state.view === "focus" || state.view === "local" ? (
          <div className="graph-focus-controls">
            <label className="field-label">
              Focus node
              <input
                className="field-control font-mono"
                list="graph-statement-ids"
                onChange={(event) => update({ node: event.target.value })}
                placeholder={view.anchor ?? "STMT-…"}
                value={state.node}
              />
            </label>
            {state.view === "focus" ? <label className="field-label">
              Hops
              <input
                className="field-control"
                max={MAX_HOPS}
                min={0}
                onChange={(event) => update({ hops: Number(event.target.value) })}
                type="number"
                value={state.hops}
              />
            </label> : null}
            {state.view === "focus" ? <label className="field-label">
              Direction
              <select
                className="field-control"
                onChange={(event) => update({ dir: event.target.value as GraphState["dir"] })}
                value={state.dir}
              >
                <option value="both">Up and down</option>
                <option value="up">Up: what it supports</option>
                <option value="down">Down: what it rests on</option>
              </select>
            </label> : null}
          </div>
        ) : null}
        {state.view === "all" && state.layout === "layered" ? (
          <div className="graph-focus-controls">
            <label className="field-label">
              Cluster by
              <select
                className="field-control"
                onChange={(event) =>
                  update({
                    cluster: event.target.value as GraphState["cluster"],
                    open: [],
                  })
                }
                value={state.cluster}
              >
                <option value="passage">Source passage</option>
                <option value="source">Source work</option>
                <option value="namespace">Lean namespace</option>
              </select>
            </label>
            {state.open.length ? (
              <button className="graph-button" onClick={() => update({ open: [] })} type="button">
                Collapse {state.open.length} cluster
                {state.open.length === 1 ? "" : "s"}
              </button>
            ) : null}
          </div>
        ) : null}
      </div>

      {state.view === "root" && stageTargets.length ? (
        <div className="graph-chip-row" aria-label="Stage targets">
          <button
            aria-pressed={target === defaultTarget}
            className="graph-chip"
            onClick={() => update({ target: "" })}
            type="button"
          >
            Root
          </button>
          {stageTargets.map(({ stage, statementId }) => (
            <button
              aria-pressed={target === statementId}
              className="graph-chip"
              key={stage}
              onClick={() => update({ target: statementId })}
              type="button"
            >
              Stage {stage}
            </button>
          ))}
        </div>
      ) : null}

      <div className="graph-filters">
        <label className="field-label">
          Source
          <select
            className="field-control"
            onChange={(event) => update({ source: event.target.value })}
            value={state.source}
          >
            <option value="">All sources</option>
            {graph.sources.map((source) => (
              <option key={source.id} value={source.id}>
                {source.author}, {source.work}
              </option>
            ))}
          </select>
        </label>
        <label className="field-label">
          Add tag
          <select
            className="field-control"
            onChange={(event) => {
              const tag = event.target.value;
              if (tag)
                update((current) => ({
                  tags: current.tags.includes(tag) ? current.tags : [...current.tags, tag],
                }));
            }}
            value=""
          >
            <option value="">Choose a tag…</option>
            {[...tagOptions].map(([group, tags]) => (
              <optgroup key={group} label={group}>
                {tags.map(({ tag, count }) => (
                  <option key={tag} value={tag}>
                    {tag} ({count})
                  </option>
                ))}
              </optgroup>
            ))}
          </select>
        </label>
        <label className="field-label">
          Root reachability
          <select className="field-control" onChange={(event) => update({ reach: event.target.value as GraphState["reach"] })} value={state.reach}>
            <option value="">Any</option>
            {REACH_FACETS.map((facet) => <option key={facet.id} value={facet.id}>{facet.label} ({facetTotals.reach[facet.id] ?? 0})</option>)}
          </select>
        </label>
        <label className="field-label">
          Add area
          <select
            className="field-control"
            onChange={(event) => { if (event.target.value) toggleFacet("area", event.target.value); }}
            value=""
          >
            <option value="">Choose an area…</option>
            {Object.entries(facetTotals.area).sort(([left], [right]) => left.localeCompare(right)).map(([area, count]) => (
              <option disabled={state.area.includes(area)} key={area} value={area}>{area} ({count})</option>
            ))}
          </select>
        </label>
      </div>
      <div className="graph-facets">
        <FacetChips label="Lane" options={LANES} selected={state.lane} counts={facetTotals.lane} toggle={(value) => toggleFacet("lane", value)} />
        <FacetChips label="Closure" options={CLOSURE_FACETS} selected={state.closure} counts={facetTotals.closure} toggle={(value) => toggleFacet("closure", value)} />
        <FacetChips label="Linked records" options={RECORD_FACETS} selected={state.rec} counts={facetTotals.rec} toggle={(value) => toggleFacet("rec", value)} />
      </div>

      <details className="graph-status-filters"><summary>Status filters and legend</summary>
      <fieldset className="graph-chip-row">
        <legend className="sr-only">Status</legend>
        {GRAPH_STATUSES.map((status) => {
          const active = state.status.includes(status.id);
          return (
            <button
              aria-pressed={active}
              className="graph-chip"
              data-status={status.id}
              key={status.id}
              onClick={() =>
                update((current) => ({
                  status: current.status.includes(status.id)
                    ? current.status.filter((entry) => entry !== status.id)
                    : [...current.status, status.id as GraphStatus],
                }))
              }
              title={status.description}
              type="button"
            >
              <span aria-hidden="true" className="graph-swatch" />
              {status.label}
            </button>
          );
        })}
      </fieldset>
      <GraphLegend />
      </details>
      </details>

      {state.tags.length || hasFilters(state) ? (
        <div className="graph-chip-row">
          {state.area.map((area) => (
            <button className="graph-chip" aria-pressed key={`area:${area}`} onClick={() => toggleFacet("area", area)} title="Remove area" type="button">
              area {area} ×
            </button>
          ))}
          {state.tags.map((tag) => (
            <button
              className="graph-chip"
              aria-pressed
              key={tag}
              onClick={() =>
                update((current) => ({
                  tags: current.tags.filter((entry) => entry !== tag),
                }))
              }
              title="Remove tag"
              type="button"
            >
              {tag} ×
            </button>
          ))}
          <label className="graph-toggle">
            <input checked={state.hide} onChange={(event) => update({ hide: event.target.checked })} type="checkbox" />
            Hide non-matching statements (otherwise dimmed)
          </label>
          <button
            className="graph-button"
            onClick={() => update({ q: "", status: [], tags: [], source: "", leaf: "", hide: false, area: [], lane: [], closure: [], rec: [], reach: "" })}
            type="button"
          >
            Clear filters
          </button>
        </div>
      ) : null}

      {search.total ? (
        <details className="graph-search" open={state.view === "all" && !state.open.length}>
          <summary>
            {search.total} matching statement{search.total === 1 ? "" : "s"} in the loaded graph
            {search.total > search.items.length ? ` (top ${search.items.length})` : ""}
          </summary>
          <ul>
            {search.items.map((statement) => (
              <li key={statement.id}>
                <span>
                  <span className="font-mono text-xs text-[var(--muted)]">{statement.id}</span>
                  <span className="block">{statement.paraphrase}</span>
                </span>
                <span className="graph-search-actions">
                  <button
                    className="graph-button"
                    onClick={() =>
                      update({
                        view: "focus",
                        node: statement.id,
                        sel: statement.id,
                        returnView: state.returnView || serializeGraphState({ ...state, returnView: "" }),
                        viewport: "",
                      })
                    }
                    type="button"
                  >
                    Focus
                  </button>
                  <button
                    className="graph-button"
                    onClick={() =>
                      update({
                        view: "root",
                        target: statement.id,
                        sel: statement.id,
                      })
                    }
                    type="button"
                  >
                    Root paths
                  </button>
                </span>
              </li>
            ))}
          </ul>
        </details>
      ) : null}

      {state.view === "all" ? (
        <details className="graph-buckets">
          <summary>
            Graph data: {buckets.shown.length} of {manifest.buckets.length} buckets shown, {graph.statements.length} of {manifest.totals.statements} statements
            {buckets.pending ? " · loading…" : ""}
          </summary>
          <p className="graph-buckets-note">Each bucket holds whole connected components, so no inference or research link is cut. The default view loads the components that reach {manifest.defaultTarget ?? "the root"}; filters skip buckets without a possible match.</p>
          <div className="graph-chip-row">
            <button className="graph-button" onClick={() => update({ buckets: [ALL_BUCKETS], showIsolated: true, viewport: "" })} type="button">Load every bucket</button>
            <button className="graph-button" disabled={!state.buckets.length} onClick={() => update({ buckets: [], viewport: "" })} type="button">Default buckets</button>
          </div>
          <ul className="graph-bucket-list">
            {manifest.buckets.map((bucket) => (
              <li key={bucket.id}>
                <label className="graph-toggle">
                  <input checked={buckets.wanted.includes(bucket.id)} onChange={() => toggleBucket(bucket.id)} type="checkbox" />
                  <span>{bucket.label}</span>
                  <span className="graph-bucket-meta">{bucket.statements} statements · {bucket.inferences} steps · {bucket.frontier} frontier</span>
                </label>
              </li>
            ))}
          </ul>
        </details>
      ) : null}

      <p aria-live="polite" className="frontier-view-status">
        {buckets.pending ? "Loading graph data… " : ""}
        {buckets.error ? `Graph data failed to load (${buckets.error}). ` : ""}
        {compact && state.view === "all" ? `${network.componentCount} inference-only components, ${network.layoutComponentCount} research-connected islands; ${graph.relations.length} recorded research links in the loaded buckets. ` : ""}
        {compact && state.view === "all" && !state.showIsolated && !hasFilters(state) ? "Singletons (readings without an inference or research link) hidden; show them under More views and filters. " : ""}
        {state.view === "local" ? `Local neighborhood: ${state.hops} ${state.hops === 1 ? "hop" : "hops"} from ${view.anchor}. ` : ""}
        {view.message ? `${view.message} ` : ""}
        {view.statementCount} of {manifest.totals.statements} statements ({manifest.totals.statements - view.statementCount} outside view), {view.nodes.filter((node) => node.kind === "inference").length} inference applications, {view.nodes.filter((node) => node.kind === "statement" && !node.matched).length} dimmed/context statements, {view.frontierCount} open premises (frontier) in view
        {view.truncated ? `; ${view.truncated} further statements not shown (narrow with hops or filters)` : ""}.
      </p>

      <div className="frontier-workspace">
        <div className="graph-layout">
          <div className="graph-shell" onKeyDownCapture={(event) => {
            if (event.key !== "Enter" && event.key !== " ") { return; }
            const element = (event.target as HTMLElement).closest<HTMLElement>(".react-flow__node");
            const node = nodes.find((entry) => entry.id === element?.dataset.id);
            if (node) { event.preventDefault(); event.stopPropagation(); onNodeClick(event, node); }
          }}>
            <div className="frontier-map-key" aria-label="Graph legend">
              <span><i className="frontier-key-dot frontier-key-open" /> Open frontier</span>
              <span><i className="frontier-key-dot frontier-key-established" /> Established</span>
              <span><i className="frontier-key-dot frontier-key-conditional" /> Conditional</span>
              <span><i className="frontier-key-dot frontier-key-other" /> Other proposition</span>
              {state.relations ? <span><i className="frontier-key-relation" /> Research link · not proof</span> : null}
            </div>
            {/* Mount the canvas once the needed buckets are in: a canvas remounted
                while data streams in can keep nodes unmeasured (hidden). */}
            {buckets.pending ? <p className="graph-loading">Loading graph data…</p> : (
            <ReactFlow
              edges={edges}
              defaultViewport={parseViewport(state.viewport)}
              fitView={!parseViewport(state.viewport) && (state.view === "local" || !(state.sel && state.obligation))}
              onMoveEnd={(event, viewport) => {
                if (event) {
                  update({
                    viewport: `${Math.round(viewport.x)},${Math.round(viewport.y)},${viewport.zoom.toFixed(4)}`,
                  });
                }
              }}
              fitViewOptions={{ padding: 0.12, minZoom: compact ? 0.05 : 0.4 }}
              key={flowKey}
              maxZoom={1.6}
              minZoom={0.05}
              nodes={nodes}
              nodesConnectable={false}
              nodesDraggable={false}
              nodeTypes={nodeTypes}
              onNodeClick={onNodeClick}
              onNodesChange={onNodesChange}
              onNodeMouseEnter={state.view === "local" && compact ? (_event, node) => setHoveredId(node.id) : undefined}
              onNodeMouseLeave={state.view === "local" && compact ? () => setHoveredId("") : undefined}
              onlyRenderVisibleElements
            >
              <SelectionLocator state={state} compact={compact} />
              <Controls showInteractive={false} />
            </ReactFlow>
            )}
          </div>
        </div>
        <div className="frontier-sidebar">
          {state.sel ? <DetailPanel graph={graph} index={index} state={state} update={update} network={network} /> : null}
          <ResearchQueue items={queue} selected={activeObligation} state={state} select={selectObligation} update={update} />
        </div>
      </div>
      <ProofExplorationControls graph={graph} target={proofTarget} state={state} start={(next) => update(next)} hide={() => update({ explore: false })} />
      {state.explore ? <ProofExplorationPanel graph={graph} result={visibleProof} running={proof.running} onCancel={proof.cancel} onFocus={(id) => update({ view: "focus", node: id, sel: id, viewport: "", returnView: state.returnView || serializeGraphState({ ...state, returnView: "" }) })} /> : null}
    </section>
  );
}

function FacetChips({
  label,
  options,
  selected,
  counts,
  toggle,
}: {
  label: string;
  options: ReadonlyArray<{ id: string; label: string; description?: string }>;
  selected: readonly string[];
  counts: Record<string, number>;
  toggle: (value: string) => void;
}) {
  return (
    <fieldset className="graph-chip-row graph-facet">
      <legend>{label}</legend>
      {options.map((option) => (
        <button
          aria-pressed={selected.includes(option.id)}
          className="graph-chip"
          key={option.id}
          onClick={() => toggle(option.id)}
          title={option.description}
          type="button"
        >
          {option.label} ({counts[option.id] ?? 0})
        </button>
      ))}
    </fieldset>
  );
}

/** Locate by the retained layout position before measurement, so a culled node can mount. */
function SelectionLocator({ state, compact }: { state: GraphState; compact: boolean }) {
  const position = useStore((store) => store.nodeLookup.get(state.sel)?.position);
  const ready = useStore((store) => store.width > 0 && store.height > 0);
  const { setCenter } = useReactFlow();
  useEffect(() => {
    if (ready && position && state.view !== "local" && !state.viewport && state.sel && state.obligation) {
      void setCenter(position.x + (compact ? 14 : NODE_SIZE.statement.width / 2), position.y + (compact ? 14 : NODE_SIZE.statement.height / 2), {
        zoom: 0.8,
      });
    }
  }, [ready, position, state.view, state.sel, state.obligation, state.viewport, setCenter, compact]);
  return null;
}

function DetailPanel({
  network,
  graph,
  index,
  state,
  update,
}: {
  graph: PropositionGraph;
  network: LoadedNetwork;
  index: ReturnType<typeof indexGraph>;
  state: GraphState;
  update: (patch: Partial<GraphState> | ((current: GraphState) => Partial<GraphState>)) => void;
}) {
  const statement = index.statementById.get(state.sel);
  const inference = index.inferenceById.get(state.sel);
  const argumentById = useMemo(() => new Map(graph.arguments.map((argument) => [argument.id, argument])), [graph]);
  const sourceById = useMemo(() => new Map(graph.sources.map((source) => [source.id, source])), [graph]);

  if (!statement && !inference) {
    return (
      <aside className="graph-detail">
        <p className="eyebrow">Details</p>
        <p className="mt-3 text-sm leading-6 text-[var(--muted)]">
          Select a statement or inference step to see its paraphrase, Lean declaration, source claims, and the arguments
          and results that use it.
        </p>
      </aside>
    );
  }

  const argumentIds = statement
    ? [...new Set([...statement.conclusionOf, ...statement.premiseOf])]
    : (inference?.argumentIds ?? []);

  const argumentList = (
    <div className="mt-6">
      <p className="eyebrow">Arguments</p>
      {argumentIds.length ? (
        <ul className="mt-2 grid gap-3 text-sm">
          {argumentIds.map((argumentId) => {
            const argument = argumentById.get(argumentId);
            if (!argument) return null;
            const role = statement
              ? argument.conclusion === statement.id
                ? "concludes"
                : "uses as premise"
              : "contains this step";
            return (
              <li key={argumentId}>
                <span className="font-mono text-xs break-all">{argumentId}</span>
                <span className="block text-[var(--muted)]">
                  {role}
                  {argument.resultIds.length
                    ? argument.transcriptionResultIds.length === argument.resultIds.length
                      ? " · verified (transcription heuristic)"
                      : " · verified"
                    : " · no result"}
                </span>
                <span className="mt-1 flex flex-wrap gap-2">
                  {argument.resultIds.map((resultId) => (
                    <Link className="link-quiet" href={`/results/${resultId}`} key={resultId}>
                      Result page
                    </Link>
                  ))}
                  <button
                    className="graph-link-button"
                    onClick={() =>
                      update({
                        arg: state.arg === argumentId ? "" : argumentId,
                      })
                    }
                    type="button"
                  >
                    {state.arg === argumentId ? "Clear highlight" : "Highlight"}
                  </button>
                </span>
              </li>
            );
          })}
        </ul>
      ) : (
        <p className="mt-2 text-sm text-[var(--muted)]">No argument uses it yet.</p>
      )}
    </div>
  );

  if (inference) {
    return (
      <aside className="graph-detail">
        <p className="eyebrow">Inference application</p>
        <h3 className="mt-2 font-serif text-2xl leading-tight">{inference.rule.replaceAll("_", " ")}</h3>
        <p className="mt-1 font-mono text-xs break-all text-[var(--muted)]">{inference.id}</p>
        <p className="mt-4 text-sm leading-6">{inference.meaning}</p>
        <p className="eyebrow mt-6">All premises (AND) → conclusion</p>
        <ul className="mt-2 grid gap-1 text-sm">
          {[...inference.inputs, ...inference.assumptions].map((id) => (
            <li key={id}>
              <button
                className="graph-link-button font-mono text-xs break-all"
                onClick={() => update({ sel: id })}
                type="button"
              >
                {id}
                {inference.assumptions.includes(id) ? " (assumption)" : ""}
              </button>
            </li>
          ))}
          <li>
            <button
              className="graph-link-button font-mono text-xs break-all"
              onClick={() => update({ sel: inference.output })}
              type="button"
            >
              ⊢ {inference.output}
            </button>
          </li>
        </ul>
        <div className="mt-4 flex flex-wrap gap-2">
          <button
            className="graph-button"
            onClick={() =>
              update({
                view: "focus",
                node: inference.id,
                returnView: state.returnView || serializeGraphState({ ...state, returnView: "" }),
                viewport: "",
              })
            }
            type="button"
          >
            Focus here
          </button>
        </div>
        {argumentList}
      </aside>
    );
  }

  const current = statement as GraphStatement;
  const community = network.community.get(current.id);
  const members = graph.statements.filter((entry) => network.community.get(entry.id) === community);
  const memberInferences = graph.inferences.filter((entry) => network.community.get(entry.id) === community).length;
  const researchConnections = graph.relations
    .filter((relation) => relation.subject !== relation.object && (relation.subject === current.id || relation.object === current.id))
    .sort((left, right) => left.id.localeCompare(right.id));
  return (
    <aside className="graph-detail">
      <p className="eyebrow">
        {statusLabel.get(current.status)}
        {current.refuted ? " · refuted" : ""}
        {current.frontier ? ` · frontier (${current.frontierDepth})` : ""}
      </p>
      <h3 className="mt-2 font-serif text-2xl leading-tight">{current.paraphrase}</h3>
      <p className="mt-1 font-mono text-xs break-all text-[var(--muted)]">{current.id}</p>
      <div className="mt-3 flex flex-wrap gap-x-4 gap-y-2 text-sm">
        <Link className="link-quiet" href={`/dossiers/${current.id}`}>
          Research dossier and attempts →
        </Link>
        <Link className="link-quiet" href={`/statements/${current.id}`}>
          Proposition and proof record →
        </Link>
      </div>
      <div className="mt-4 flex flex-wrap gap-2">
        <button
          className="graph-button"
          onClick={() => update({
            view: "local", layout: "network", node: current.id, scope: "global", viewport: "",
            returnView: state.returnView || serializeGraphState({ ...state, returnView: "" }),
          })}
          type="button"
        >
          Local graph
        </button>
        <button
          className="graph-button"
          onClick={() =>
            update({
              view: "focus",
              node: current.id,
              returnView: state.returnView || serializeGraphState({ ...state, returnView: "" }),
              viewport: "",
            })
          }
          type="button"
        >
          Focus here
        </button>
        <button className="graph-button" onClick={() => update({ view: "root", target: current.id })} type="button">
          Paths into this
        </button>
      </div>
      <button
        className="graph-button mt-3"
        onClick={() =>
          update((state) => ({
            expanded: [...new Set([...state.expanded, current.id])],
          }))
        }
        type="button"
      >
        Expand dependencies and consequences
      </button>
      <dl className="mt-6 grid gap-3 text-sm">
        <div>
          <dt className="eyebrow">Epistemic scope</dt>
          <dd>
            {current.established
              ? "Established in the encoded premise program"
              : current.closureReason
                ? "Closed by formal consequence; premises not established"
                : current.frontier
                  ? "Open premise"
                  : "No establishment recorded"}
            . Source integrity and interpretation fidelity are separate; inspect the linked claims and witnesses.
          </dd>
        </div>
        <div>
          <dt className="eyebrow">Connectivity community {community}</dt>
          <dd>{members.length} statements, {memberInferences} inference applications; {members.filter((entry) => entry.established).length} established, {members.filter((entry) => !entry.established && entry.closureReason).length} conditionally closed, {members.filter((entry) => !entry.established && !entry.closureReason).length} without recorded closure, {members.filter((entry) => entry.frontier).length} frontier. Counts describe recorded structure, not confidence.</dd>
        </div>
        <div>
          <dt className="eyebrow">Structural leaves</dt>
          <dd>{network.unsupported.has(current.id) ? "No known supporting inference. " : "Has supporting inferences. "}{network.unconsumed.has(current.id) ? "No known dependent inference." : "Has dependent inferences."} These are independent of frontier status.</dd>
        </div>
        <div>
          <dt className="eyebrow">Inference connectivity</dt>
          <dd>{new Set([...(index.producers.get(current.id) ?? []), ...(index.consumers.get(current.id) ?? [])].map((step) => step.id)).size} incident applications; {index.producers.get(current.id)?.length ?? 0} supporting alternatives (OR); {index.consumers.get(current.id)?.length ?? 0} consumers. Each application requires all its premises (AND).</dd>
        </div>
        <div>
          <dt className="eyebrow">Recorded research links ({researchConnections.length})</dt>
          <dd className="mt-1 text-[var(--muted)]">These are objections, alternatives, or source/argument evidence, never additional inference steps.</dd>
          {researchConnections.length ? (
            <ul className="mt-2 grid max-h-64 gap-3 overflow-y-auto">
              {researchConnections.map((relation) => {
                const outbound = relation.subject === current.id;
                const peer = outbound ? relation.object : relation.subject;
                const peerStatement = index.statementById.get(peer);
                let originHref = `/statements/${relation.originId}`;
                if (relation.originKind === "claim") {
                  originHref = `/claims/${relation.originId}`;
                } else if (relation.originKind === "argument") {
                  const argument = argumentById.get(relation.originId);
                  originHref = argument?.resultIds[0]
                    ? `/results/${argument.resultIds[0]}`
                    : `/statements/${argument?.conclusion ?? relation.subject}`;
                }
                return (
                  <li className="border-l-2 border-[var(--status-alternative)] pl-2" key={relation.id}>
                    <span className="block text-xs text-[var(--muted)]">{outbound ? "→" : "←"} {relation.predicate.replaceAll("_", " ")} · {relation.originKind} record</span>
                    <button className="graph-link-button mt-1 text-left text-sm" onClick={() => update((state) => ({
                      sel: peer,
                      viewport: "",
                      expanded: [...new Set([...state.expanded, peer])],
                    }))} type="button">
                      {peerStatement?.paraphrase ?? peer}
                    </button>
                    <span className="mt-1 block text-xs">
                      <Link className="link-quiet" href={originHref}>
                        {relation.originId} →
                      </Link>
                    </span>
                    {relation.note ? <span className="mt-1 block text-xs text-[var(--muted)]">{relation.note}</span> : null}
                  </li>
                );
              })}
            </ul>
          ) : null}
        </div>
        <div>
          <dt className="eyebrow">Lean declaration</dt>
          <dd className="mt-1 font-mono text-xs break-all">{current.leanDeclaration ?? "None"}</dd>
        </div>
        {current.frontier ? (
          <div>
            <dt className="eyebrow">Dependents</dt>
            <dd className="mt-1">
              {current.premiseOf.length} direct, {current.transitiveDependentArguments} transitive arguments
            </dd>
          </div>
        ) : null}
        {current.floor ? (
          <div data-floor-basis={current.floor.basis} data-floor-met={current.floor.met}>
            <dt className="eyebrow">Floor marking · {current.floor.basis}</dt>
            <dd className="mt-1">
              {current.floor.met
                ? "Criterion holds on the current records; the marking closes it."
                : `Criterion fails, so the marking closes nothing: ${current.floor.reasons.join("; ")}.`}
            </dd>
            <dd className="mt-1 text-xs text-[var(--muted)]">Disagreement: {describeDisagreement(current.floor.disagreement)}</dd>
            <dd className="mt-1 font-mono text-xs break-all">Justified by {current.floor.justification_ids.join(", ")}</dd>
          </div>
        ) : null}
        {current.closedViaTranscription ? (
          <div>
            <dt className="eyebrow">Closed via transcription from closed premises</dt>
            <dd className="mt-1 font-mono text-xs break-all">
              {current.closedViaTranscription.resultId} (
              {current.closedViaTranscription.premises.join(", ") || "no premises"})
            </dd>
          </div>
        ) : null}
        <div>
          <dt className="eyebrow">Tags</dt>
          <dd className="mt-1 flex flex-wrap gap-1">
            {current.tags.map((tag) => (
              <button
                className="graph-badge graph-badge-button"
                key={tag}
                onClick={() =>
                  update((current) => ({
                    tags: current.tags.includes(tag) ? current.tags : [...current.tags, tag],
                  }))
                }
                title="Filter by this tag"
                type="button"
              >
                {tag}
              </button>
            ))}
          </dd>
        </div>
      </dl>
      <div className="mt-6">
        <p className="eyebrow">Source claims</p>
        {current.claims.length ? (
          <ul className="mt-2 grid gap-4 text-sm">
            {current.claims.map((claim) => {
              const source = sourceById.get(claim.sourceId);
              return (
                <li key={claim.id}>
                  <Link className="link-quiet font-mono text-xs break-all" href={`/claims/${claim.id}`}>
                    {claim.id}
                  </Link>
                  {claim.reading ? <span className="text-[var(--muted)]"> · reading {claim.reading}</span> : null}
                  <span className="block">
                    <Link className="link-quiet" href={`/sources/${claim.sourceId}`}>
                      {source ? `${source.author}, ${source.work}` : claim.sourceId}
                    </Link>
                    , {claim.locator}
                  </span>
                  <span className="mt-1 block leading-6 text-[var(--muted)]">{claim.interpretation}</span>
                </li>
              );
            })}
          </ul>
        ) : (
          <p className="mt-2 text-sm text-[var(--muted)]">No source claim recorded.</p>
        )}
      </div>
      {argumentList}
    </aside>
  );
}

function GraphLegend() {
  return (
    <div className="graph-legend">
      <p className="eyebrow">Reading the graph</p>
      <p className="mt-2 max-w-3xl text-sm leading-6 text-[var(--muted)]">
        Each round dot is a proposition. A small square is an inference junction: every input is required together, not an independent pairwise implication. Amber rings mark the recorded frontier: open premises, with red rings for bare premises lacking source support. Green rings distinguish established statements; hollow blue rings mark conditionally closed deductions whose premises might still be open. Center colors indicate connectivity communities, not philosophical agreement, truth, or confidence. Dot size shows incident inference degree. Selection highlights immediate dependencies and consequences; Focus follows further paths. Structural leaves and epistemic obligations are distinct. In layered mode, premises sit below the inference steps that use them, and conclusions above. Every logical step goes through
        an explicit inference node; dashed purple links record source, objection or alternative relationships (never logical entailment). A claim or argument link is projected through its statement, with the original record visible in the inspector. Research links affect map proximity but not inference connectivity or closure. Dotted edges summarize steps
        into a collapsed cluster. Status says only how a statement stands inside the corpus: a verified result checks
        formal consequence, not premise truth or source fidelity; the transcription flag is a textual heuristic. The frontier is the highlighted set of unresolved propositions, not a fabricated geometric boundary.
      </p>
      <ul className="mt-4 grid gap-2 text-sm sm:grid-cols-2 lg:grid-cols-3">
        {GRAPH_STATUSES.map((status) => (
          <li className="flex gap-2" data-status={status.id} key={status.id}>
            <span aria-hidden="true" className="graph-swatch mt-1.5" />
            <span>
              <strong className="font-semibold">{status.label}.</strong>{" "}
              <span className="text-[var(--muted)]">{status.description}</span>
            </span>
          </li>
        ))}
      </ul>
    </div>
  );
}
