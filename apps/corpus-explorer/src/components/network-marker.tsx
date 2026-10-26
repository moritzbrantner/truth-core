import { Handle, Position, type Node, type NodeProps } from "@xyflow/react";
import type { ProofOverlay } from "@/lib/proof-overlay";
import type { ViewNode } from "@/lib/graph-view";

export type NetworkMarkerData = {
  view: ViewNode;
  selected: boolean;
  proof?: ProofOverlay;
  community: number;
  degree: number;
  emphasis: "frontier" | "all";
} & Record<string, unknown>;

const colors = ["#456787", "#865b3f", "#5d6e3f", "#755c89", "#337571", "#914f67", "#736934", "#515e88"];

export function NetworkMarker({ data }: NodeProps<Node<NetworkMarkerData>>) {
  const node = data.view;
  if (node.kind === "cluster") { return null; }
  const statement = node.kind === "statement" ? node.statement : undefined;
  const title = node.kind === "statement" ? node.statement.paraphrase : node.inference.meaning;
  return (
    <div
      className="network-marker"
      data-proof-target={data.proof?.target ?? false}
      data-proof-forward={data.proof?.forward ?? false}
      data-proof-backward={data.proof?.backward ?? false}
      data-proof-junction={data.proof?.junction ?? false}
      data-proof-blocker={data.proof?.blocker ?? false}
      data-kind={node.kind}
      data-selected={data.selected}
      data-highlighted={node.highlighted}
      data-hover-dimmed={data.hoverDimmed === true}
      data-hover-neighbor={data.hoverNeighbor === true}
      data-dimmed={!node.matched}
      data-frontier={statement?.frontier}
      data-frontier-depth={statement?.frontierDepth ?? ""}
      data-established={statement?.established}
      data-conditional={Boolean(statement?.closureReason && !statement.established)}
      data-refuted={statement?.refuted}
      data-emphasis={data.emphasis}
      title={`${node.id}: ${title}. ${data.degree} incident inference connections`}
      style={{ "--community": colors[data.community % colors.length], "--marker-size": `${Math.min(20, 9 + Math.sqrt(data.degree) * 1.8)}px` } as React.CSSProperties}
    >
      <Handle position={Position.Bottom} type="target" />
      <span aria-hidden="true" className="network-symbol" />
      <span className="network-label" data-visible={data.selected}>{title}</span>
      <Handle position={Position.Top} type="source" />
    </div>
  );
}
