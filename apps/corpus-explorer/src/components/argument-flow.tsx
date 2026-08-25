"use client";

import {
  Background,
  Controls,
  Handle,
  MarkerType,
  Panel,
  Position,
  ReactFlow,
  type Edge,
  type Node,
  type NodeProps,
} from "@xyflow/react";
import { useMemo, useState } from "react";

import {
  projectArgumentComposition,
  type ArgumentProjectionCorpus,
  type ProjectedArgumentNode,
} from "@/lib/argument-projection";

type ArgumentFlowNodeData = ProjectedArgumentNode & {
  onToggle: (argumentId: string) => void;
} & Record<string, unknown>;

type ArgumentFlowNode = Node<ArgumentFlowNodeData, "argument">;

type ArgumentFlowProps = {
  corpus: ArgumentProjectionCorpus;
  rootArgumentId: string;
};

const nodeTypes = {
  argument: ArgumentNode,
};

function ArgumentNode({ data }: NodeProps<ArgumentFlowNode>) {
  const intermediateOutputs = data.steps
    .map((step) => step.output)
    .filter(
      (statement, index, all) =>
        statement.id !== data.conclusion.id &&
        !data.premises.some((premise) => premise.id === statement.id) &&
        all.findIndex((candidate) => candidate.id === statement.id) === index,
    );

  return (
    <div className="argument-flow-node" data-expanded={data.expanded ? "true" : "false"}>
      <Handle type="target" position={Position.Top} />
      <button
        aria-expanded={data.expanded}
        className="argument-flow-node-header nodrag"
        onClick={() => data.onToggle(data.argumentId)}
        type="button"
      >
        <span>
          <span className="eyebrow">{data.verified ? "Verified argument" : "Argument"}</span>
          <strong>{data.conclusion.paraphrase}</strong>
        </span>
        <span aria-hidden="true" className="argument-flow-toggle">
          {data.expanded ? "−" : "+"}
        </span>
      </button>

      {data.expanded ? (
        <div className="argument-flow-proof">
          <aside className="argument-flow-inference">
            <span aria-hidden="true" className="argument-flow-symbol">+</span>
            <span className="eyebrow">Inference</span>
            {data.steps.length === 1 ? (
              <p>{data.steps[0].rule}</p>
            ) : (
              <ol>
                {data.steps.map((step) => (
                  <li key={step.id}>{step.rule}</li>
                ))}
              </ol>
            )}
          </aside>

          <div className="argument-flow-statements">
            <div className="argument-flow-stack">
              {data.premises.map((premise, index) => (
                <div className="argument-flow-statement" key={premise.id}>
                  <span className="eyebrow">Premise {index + 1}</span>
                  <p>{premise.paraphrase}</p>
                </div>
              ))}
            </div>

            {intermediateOutputs.length ? (
              <div className="argument-flow-stack argument-flow-intermediate">
                {intermediateOutputs.map((statement) => (
                  <div className="argument-flow-statement" key={statement.id}>
                    <span className="eyebrow">Derived</span>
                    <p>{statement.paraphrase}</p>
                  </div>
                ))}
              </div>
            ) : null}

            <div className="argument-flow-conclusion">
              <span className="eyebrow">Conclusion</span>
              <p>{data.conclusion.paraphrase}</p>
            </div>
          </div>
        </div>
      ) : (
        <p className="argument-flow-summary">{data.meaning}</p>
      )}
      <Handle type="source" position={Position.Bottom} />
    </div>
  );
}

function toFlowNodes(
  projectedNodes: ProjectedArgumentNode[],
  onToggle: (argumentId: string) => void,
): ArgumentFlowNode[] {
  const levels = new Map<number, ProjectedArgumentNode[]>();
  for (const node of projectedNodes) {
    const entries = levels.get(node.depth) ?? [];
    entries.push(node);
    levels.set(node.depth, entries);
  }

  const maxDepth = Math.max(0, ...projectedNodes.map((node) => node.depth));
  const horizontalGap = 500;
  const verticalGap = 500;

  return projectedNodes.map((node) => {
    const siblings = levels.get(node.depth) ?? [node];
    const index = siblings.findIndex((candidate) => candidate.id === node.id);
    const x = (index - (siblings.length - 1) / 2) * horizontalGap;
    const y = (maxDepth - node.depth) * verticalGap;

    return {
      id: node.id,
      type: "argument",
      position: { x, y },
      data: { ...node, onToggle },
      draggable: false,
      selectable: false,
      style: { width: 430 },
    };
  });
}

function toFlowEdges(projectedEdges: ReturnType<typeof projectArgumentComposition>["edges"]): Edge[] {
  return projectedEdges.map((edge) => ({
    id: edge.id,
    source: edge.source,
    target: edge.target,
    type: "smoothstep",
    label: edge.cycle ? "cycle" : undefined,
    style: {
      stroke: edge.cycle ? "var(--accent)" : "var(--line-strong)",
      strokeDasharray: edge.cycle ? "6 6" : undefined,
    },
    markerEnd: {
      type: MarkerType.ArrowClosed,
      color: edge.cycle ? "var(--accent)" : "var(--line-strong)",
    },
  }));
}

export function ArgumentFlow({ corpus, rootArgumentId }: ArgumentFlowProps) {
  const [expandedArgumentIds, setExpandedArgumentIds] = useState<Set<string>>(
    () => new Set([rootArgumentId]),
  );

  const projection = useMemo(
    () => projectArgumentComposition(corpus, rootArgumentId, expandedArgumentIds),
    [corpus, expandedArgumentIds, rootArgumentId],
  );

  function toggleArgument(argumentId: string) {
    setExpandedArgumentIds((current) => {
      const next = new Set(current);
      if (next.has(argumentId)) {
        next.delete(argumentId);
      } else {
        next.add(argumentId);
      }
      return next;
    });
  }

  const nodes = useMemo(
    () => toFlowNodes(projection.nodes, toggleArgument),
    [projection.nodes],
  );
  const edges = useMemo(() => toFlowEdges(projection.edges), [projection.edges]);

  return (
    <div className="argument-flow-shell">
      <ReactFlow
        edges={edges}
        fitView
        fitViewOptions={{ padding: 0.18 }}
        maxZoom={1.5}
        minZoom={0.35}
        nodes={nodes}
        nodesConnectable={false}
        nodesDraggable={false}
        nodeTypes={nodeTypes}
      >
        <Background gap={24} size={1} />
        <Controls showInteractive={false} />
        <Panel className="argument-flow-actions" position="top-right">
          <button
            onClick={() => setExpandedArgumentIds(new Set(corpus.arguments.map((argument) => argument.id)))}
            type="button"
          >
            Expand all
          </button>
          <button onClick={() => setExpandedArgumentIds(new Set())} type="button">
            Collapse all
          </button>
        </Panel>
      </ReactFlow>
    </div>
  );
}
