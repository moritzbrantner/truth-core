import { Handle, Position, useStore, type Node, type NodeProps } from "@xyflow/react";
import type { ProofOverlay } from "@/lib/proof-overlay";
import type { ViewNode } from "@/lib/graph-view";

export type NetworkMarkerData = {
  view: ViewNode;
  selected: boolean;
  proof?: ProofOverlay;
  community: number;
  degree: number;
} & Record<string, unknown>;

const colors = ["#456787", "#865b3f", "#5d6e3f", "#755c89", "#337571", "#914f67", "#736934", "#515e88"];

export function NetworkMarker({ data }: NodeProps<Node<NetworkMarkerData>>) {
  const zoomed = useStore((store) => store.transform[2] > 1.1);
  const node = data.view;
  if (node.kind === "cluster") { return null; }
  const statement = node.kind === "statement" ? node.statement : undefined;
  const title = node.kind === "statement" ? node.statement.paraphrase : node.inference.meaning;
  let symbol = "○";
  if (statement?.established) { symbol = "✓"; }
  else if (statement?.closureReason) { symbol = "◐"; }
  else if (statement?.frontierDepth === "bare") { symbol = "!"; }
  else if (statement?.frontierDepth === "sourced") { symbol = "?"; }
  if (statement?.status === "transcription" && !statement.closureReason) { symbol = "T"; }
  if (statement?.status === "alternative" || statement?.status === "objection") { symbol = "◇"; }
  if (statement?.refuted) { symbol = "×"; }
  if (node.kind === "inference") { symbol = "⊢"; }
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
      data-dimmed={!node.matched}
      data-frontier={statement?.frontier}
      data-established={statement?.established}
      title={`${node.id}: ${title}. ${data.degree} incident inference connections`}
      style={{ "--community": colors[data.community % colors.length], "--marker-size": `${Math.min(26, 15 + Math.sqrt(data.degree) * 2)}px` } as React.CSSProperties}
    >
      <Handle position={Position.Bottom} type="target" />
      <span className="network-symbol">{symbol}</span>
      <span className="network-label" data-visible={zoomed || data.selected}>{title}</span>
      <Handle position={Position.Top} type="source" />
    </div>
  );
}
