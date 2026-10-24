"use client";

import {
  Background,
  Controls,
  Handle,
  MarkerType,
  Position,
  ReactFlow,
  type Edge,
  type Node,
  type NodeProps,
} from "@xyflow/react";
import Link from "next/link";
import { usePathname, useRouter, useSearchParams } from "next/navigation";
import { useEffect, useMemo, useRef } from "react";

import { layeredLayout } from "@/lib/graph-layout";
import {
  MAX_HOPS,
  hasFilters,
  parseGraphState,
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
  STAGE_CONCLUSIONS,
  type GraphStatement,
  type GraphStatus,
  type PropositionGraph,
} from "@/lib/proposition-graph";

const statusLabel = new Map(GRAPH_STATUSES.map((status) => [status.id, status.label]));

const NODE_SIZE = {
  statement: { width: 280, height: 132 },
  inference: { width: 190, height: 46 },
  cluster: { width: 250, height: 104 },
} as const;

type FlowData = { view: ViewNode; selected: boolean } & Record<string, unknown>;
type FlowNode = Node<FlowData>;

function StatementNodeView({ data }: NodeProps<FlowNode>) {
  const node = data.view as ViewStatementNode;
  const statement = node.statement;
  const provenance = statement.claims.slice(0, 2);
  return (
    <div
      className="graph-node graph-node-statement"
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
          {statusLabel.get(statement.status)}
          {statement.refuted ? " · refuted" : ""}
          {statement.frontier
            ? ` · frontier (${statement.frontierDepth}) · ${statement.transitiveDependentArguments} dependent`
            : ""}
        </span>
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

function hashIds(nodes: ViewNode[]) {
  let hash = 0;
  for (const node of nodes) {
    for (let index = 0; index < node.id.length; index += 1) {
      hash = (hash * 31 + node.id.charCodeAt(index)) | 0;
    }
  }
  return `${nodes.length}:${hash}`;
}

export function PropositionGraphExplorer({ graph }: { graph: PropositionGraph }) {
  const pathname = usePathname();
  const router = useRouter();
  const searchParams = useSearchParams();
  const state = useMemo(() => parseGraphState(searchParams), [searchParams]);
  const index = useMemo(() => indexGraph(graph), [graph]);
  const view = useMemo(() => computeGraphView(graph, state, index), [graph, state, index]);
  const search = useMemo(() => searchStatements(graph, state, 12), [graph, state]);

  // Compose updates issued before the previous router.replace commits.
  const pendingState = useRef<GraphState | null>(null);
  useEffect(() => {
    pendingState.current = null;
  }, [searchParams]);
  // Array-valued fields take a function of the pending state so rapid clicks compose.
  const update = (patch: Partial<GraphState> | ((current: GraphState) => Partial<GraphState>)) => {
    const current = pendingState.current ?? state;
    const next = { ...current, ...(typeof patch === "function" ? patch(current) : patch) };
    pendingState.current = next;
    const query = serializeGraphState(next);
    router.replace(query ? `${pathname}?${query}` : pathname, { scroll: false });
  };

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

  const { nodes, edges } = useMemo(() => {
    const positions = layeredLayout(
      view.nodes.map((node) => ({ id: node.id, ...NODE_SIZE[node.kind] })),
      view.edges.filter((edge) => edge.kind !== "relation"),
    );
    const flowNodes: FlowNode[] = view.nodes.map((node) => ({
      id: node.id,
      type: node.kind,
      position: positions.get(node.id) ?? { x: 0, y: 0 },
      data: {
        view: node,
        selected: node.id === state.sel,
      },
      draggable: false,
      selectable: false,
      style: { width: NODE_SIZE[node.kind].width },
    }));
    const flowEdges: Edge[] = view.edges.map((edge) => ({
      id: edge.id,
      source: edge.source,
      target: edge.target,
      type: edge.kind === "relation" ? "default" : "smoothstep",
      label: edge.label,
      style: { ...edgeStyle[edge.kind], strokeWidth: edge.highlighted ? 2.5 : 1.25 },
      markerEnd:
        edge.kind === "premise" || edge.kind === "assumption"
          ? undefined
          : { type: MarkerType.ArrowClosed, color: String(edgeStyle[edge.kind].stroke) },
    }));
    return { nodes: flowNodes, edges: flowEdges };
  }, [view, state.sel]);

  const onNodeClick = (_event: React.MouseEvent, node: FlowNode) => {
    const clicked = node.data.view;
    if (clicked.kind === "cluster") {
      update((current) => ({
        open: current.open.includes(clicked.key) ? current.open : [...current.open, clicked.key],
      }));
    } else {
      update({ sel: clicked.id === state.sel ? "" : clicked.id });
    }
  };

  const defaultTarget = graph.defaultTarget ?? "";
  const target = state.target || defaultTarget;
  const stageTargets = STAGE_CONCLUSIONS.filter(({ statementId }) => index.statementById.has(statementId));
  const flowKey = `${state.view}:${view.anchor}:${state.cluster}:${hashIds(view.nodes)}`;

  return (
    <section aria-labelledby="graph-heading" className="mt-10">
      <h2 className="sr-only" id="graph-heading">
        Proposition graph
      </h2>
      <datalist id="graph-statement-ids">
        {graph.statements.map((statement) => (
          <option key={statement.id} value={statement.id} />
        ))}
      </datalist>

      <div className="graph-toolbar">
        <div aria-label="View" className="graph-segmented" role="group">
          {(
            [
              ["root", "Root paths"],
              ["focus", "Focus"],
              ["all", "Full graph"],
            ] as const
          ).map(([id, label]) => (
            <button aria-pressed={state.view === id} key={id} onClick={() => update({ view: id })} type="button">
              {label}
            </button>
          ))}
        </div>

        {state.view === "root" ? (
          <label className="field-label">
            Target statement
            <input
              className="field-control font-mono"
              list="graph-statement-ids"
              onChange={(event) => update({ target: event.target.value === defaultTarget ? "" : event.target.value })}
              placeholder={defaultTarget}
              value={state.target}
            />
          </label>
        ) : null}
        {state.view === "focus" ? (
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
            <label className="field-label">
              Hops
              <input
                className="field-control"
                max={MAX_HOPS}
                min={0}
                onChange={(event) => update({ hops: Number(event.target.value) })}
                type="number"
                value={state.hops}
              />
            </label>
            <label className="field-label">
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
            </label>
          </div>
        ) : null}
        {state.view === "all" ? (
          <div className="graph-focus-controls">
            <label className="field-label">
              Cluster by
              <select
                className="field-control"
                onChange={(event) => update({ cluster: event.target.value as GraphState["cluster"], open: [] })}
                value={state.cluster}
              >
                <option value="passage">Source passage</option>
                <option value="source">Source work</option>
                <option value="namespace">Lean namespace</option>
              </select>
            </label>
            {state.open.length ? (
              <button className="graph-button" onClick={() => update({ open: [] })} type="button">
                Collapse {state.open.length} cluster{state.open.length === 1 ? "" : "s"}
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
          Search IDs and paraphrases
          <input
            className="field-control"
            onChange={(event) => update({ q: event.target.value })}
            placeholder="e.g. unmoved mover"
            type="search"
            value={state.q}
          />
        </label>
        <label className="field-label">
          Source
          <select className="field-control" onChange={(event) => update({ source: event.target.value })} value={state.source}>
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
              if (tag) update((current) => ({ tags: current.tags.includes(tag) ? current.tags : [...current.tags, tag] }));
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
      </div>

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

      {state.tags.length || hasFilters(state) ? (
        <div className="graph-chip-row">
          {state.tags.map((tag) => (
            <button
              className="graph-chip"
              aria-pressed
              key={tag}
              onClick={() => update((current) => ({ tags: current.tags.filter((entry) => entry !== tag) }))}
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
            onClick={() => update({ q: "", status: [], tags: [], source: "", hide: false })}
            type="button"
          >
            Clear filters
          </button>
        </div>
      ) : null}

      {search.total ? (
        <details className="graph-search" open={state.view === "all" && !state.open.length}>
          <summary>
            {search.total} matching statement{search.total === 1 ? "" : "s"} in the corpus
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
                  <button className="graph-button" onClick={() => update({ view: "focus", node: statement.id, sel: statement.id })} type="button">
                    Focus
                  </button>
                  <button className="graph-button" onClick={() => update({ view: "root", target: statement.id, sel: statement.id })} type="button">
                    Root paths
                  </button>
                </span>
              </li>
            ))}
          </ul>
        </details>
      ) : null}

      <p aria-live="polite" className="mt-4 text-sm text-[var(--muted)]">
        {view.message ? `${view.message} ` : ""}
        {view.statementCount} statements, {view.frontierCount} open premises (frontier) in view
        {view.truncated ? `; ${view.truncated} further statements not shown (narrow with hops or filters)` : ""}.
      </p>

      <div className="graph-layout">
        <div className="graph-shell">
          <ReactFlow
            edges={edges}
            fitView
            fitViewOptions={{ padding: 0.12, minZoom: 0.4 }}
            key={flowKey}
            maxZoom={1.6}
            minZoom={0.05}
            nodes={nodes}
            nodesConnectable={false}
            nodesDraggable={false}
            nodeTypes={nodeTypes}
            onNodeClick={onNodeClick}
            onlyRenderVisibleElements
          >
            <Background gap={24} size={1} />
            <Controls showInteractive={false} />
          </ReactFlow>
        </div>
        <DetailPanel graph={graph} index={index} state={state} update={update} />
      </div>

      <GraphLegend />
    </section>
  );
}

function DetailPanel({
  graph,
  index,
  state,
  update,
}: {
  graph: PropositionGraph;
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
          Select a statement or inference step to see its paraphrase, Lean declaration, source claims, and the arguments and results that use it.
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
                    onClick={() => update({ arg: state.arg === argumentId ? "" : argumentId })}
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
        <p className="eyebrow mt-6">Premises → conclusion</p>
        <ul className="mt-2 grid gap-1 text-sm">
          {[...inference.inputs, ...inference.assumptions].map((id) => (
            <li key={id}>
              <button className="graph-link-button font-mono text-xs break-all" onClick={() => update({ sel: id })} type="button">
                {id}
                {inference.assumptions.includes(id) ? " (assumption)" : ""}
              </button>
            </li>
          ))}
          <li>
            <button className="graph-link-button font-mono text-xs break-all" onClick={() => update({ sel: inference.output })} type="button">
              ⊢ {inference.output}
            </button>
          </li>
        </ul>
        <div className="mt-4 flex flex-wrap gap-2">
          <button className="graph-button" onClick={() => update({ view: "focus", node: inference.id })} type="button">
            Focus here
          </button>
        </div>
        {argumentList}
      </aside>
    );
  }

  const current = statement as GraphStatement;
  return (
    <aside className="graph-detail">
      <p className="eyebrow">
        {statusLabel.get(current.status)}
        {current.refuted ? " · refuted" : ""}
        {current.frontier ? ` · frontier (${current.frontierDepth})` : ""}
      </p>
      <h3 className="mt-2 font-serif text-2xl leading-tight">{current.paraphrase}</h3>
      <p className="mt-1 font-mono text-xs break-all text-[var(--muted)]">{current.id}</p>
      <div className="mt-4 flex flex-wrap gap-2">
        <button className="graph-button" onClick={() => update({ view: "focus", node: current.id })} type="button">
          Focus here
        </button>
        <button className="graph-button" onClick={() => update({ view: "root", target: current.id })} type="button">
          Paths into this
        </button>
      </div>
      <dl className="mt-6 grid gap-3 text-sm">
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
        {current.selfEvidentJustification.length ? (
          <div>
            <dt className="eyebrow">Self-evidence justified by</dt>
            <dd className="mt-1 font-mono text-xs break-all">{current.selfEvidentJustification.join(", ")}</dd>
          </div>
        ) : null}
        {current.closedViaTranscription ? (
          <div>
            <dt className="eyebrow">Closed via transcription from closed premises</dt>
            <dd className="mt-1 font-mono text-xs break-all">
              {current.closedViaTranscription.resultId} ({current.closedViaTranscription.premises.join(", ") || "no premises"})
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
                onClick={() => update((current) => ({ tags: current.tags.includes(tag) ? current.tags : [...current.tags, tag] }))}
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
          <p className="mt-2 text-sm text-[var(--muted)]">No source claim: a derived statement.</p>
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
        Premises sit below the inference steps (⊢) that use them, and conclusions above. Every logical step goes through an explicit inference node; dashed coloured edges are relations, never support. Dotted edges summarize steps into a collapsed cluster. Status says only how a statement stands inside the corpus: a verified result checks formal consequence, not premise truth or source fidelity, and the transcription flag is a textual heuristic.
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
