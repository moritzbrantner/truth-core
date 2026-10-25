import { forceCenter, forceCollide, forceLink, forceManyBody, forceSimulation, type SimulationNodeDatum } from "d3-force";
import type { PropositionGraph } from "./proposition-graph";
import type { Point } from "./graph-layout";
import { indexGraph } from "./graph-view";

export const NETWORK_TICKS = 180;
export type NetworkStructure = {
  positions: Map<string, Point>;
  community: Map<string, number>;
  degree: Map<string, number>;
  unsupported: Set<string>;
  unconsumed: Set<string>;
  components: string[][];
};

/** Presentation only: relations and epistemic status never enter the force graph.
 * Sorted input, D3's fixed default random seed, and a bounded stopped simulation
 * give reproducible positions. Compute on the whole corpus, never the filter.
 */
export function networkStructure(graph: PropositionGraph): NetworkStructure {
  const index = indexGraph(graph);
  const ids = [...graph.statements.map((node) => node.id), ...graph.inferences.map((node) => node.id)].sort();
  const neighbours = new Map(ids.map((id) => [id, new Set<string>()]));
  const links: Array<{ source: string; target: string }> = [];
  const connect = (source: string, target: string) => {
    if (!neighbours.has(source) || !neighbours.has(target)) { return; }
    neighbours.get(source)?.add(target);
    neighbours.get(target)?.add(source);
    links.push({ source, target });
  };
  for (const inference of [...graph.inferences].sort((a, b) => a.id.localeCompare(b.id))) {
    for (const id of [...new Set([...inference.inputs, ...inference.assumptions])].sort()) { connect(id, inference.id); }
    connect(inference.id, inference.output);
  }
  const components: string[][] = [];
  const visited = new Set<string>();
  for (const id of ids) {
    if (visited.has(id)) { continue; }
    const component = [id];
    visited.add(id);
    for (let cursor = 0; cursor < component.length; cursor += 1) {
      for (const other of neighbours.get(component[cursor]) ?? []) {
        if (!visited.has(other)) { visited.add(other); component.push(other); }
      }
    }
    components.push(component.sort());
  }
  components.sort((a, b) => b.length - a.length || a[0].localeCompare(b[0]));
  // Deterministic label propagation uses only incident inference connectivity.
  const labels = new Map(ids.map((id, i) => [id, i]));
  for (let round = 0; round < 8; round += 1) {
    for (const id of ids) {
      const votes = new Map<number, number>();
      for (const other of neighbours.get(id) ?? []) {
        const label = labels.get(other)!;
        votes.set(label, (votes.get(label) ?? 0) + 1);
      }
      const best = [...votes].sort((a, b) => b[1] - a[1] || a[0] - b[0])[0];
      if (best) { labels.set(id, best[0]); }
    }
  }
  const labelIds = [...new Set(labels.values())].sort((a, b) => a - b);
  const community = new Map(ids.map((id) => [id, labelIds.indexOf(labels.get(id)!)]));
  const positions = new Map<string, Point>();
  // Pack disconnected components into shelves, preserving islands rather than
  // letting an unconstrained global charge scatter them into a vast canvas.
  let shelfX = 0; let shelfY = 0; let shelfHeight = 0;
  const shelfWidth = Math.max(1000, Math.sqrt(ids.length) * 72);
  for (const component of components) {
    if (component.length === 1) {
      if (shelfX + 40 > shelfWidth) { shelfX = 0; shelfY += shelfHeight; shelfHeight = 0; }
      positions.set(component[0], { x: shelfX, y: shelfY });
      shelfX += 40; shelfHeight = Math.max(shelfHeight, 40);
      continue;
    }
    const members = new Set(component);
    const nodes: Array<SimulationNodeDatum & { id: string }> = component.map((id) => ({ id }));
    const edges = links.filter((link) => members.has(link.source)).map((link) => ({ ...link }));
    const simulation = forceSimulation(nodes).stop()
      .force("link", forceLink(edges).id((node) => (node as SimulationNodeDatum & { id: string }).id).distance(35).strength(0.65))
      .force("charge", forceManyBody().strength(-65).distanceMax(500))
      .force("collision", forceCollide(11))
      .force("center", forceCenter());
    simulation.tick(NETWORK_TICKS);
    const minX = Math.min(...nodes.map((node) => node.x ?? 0));
    const minY = Math.min(...nodes.map((node) => node.y ?? 0));
    const width = Math.max(32, ...nodes.map((node) => (node.x ?? 0) - minX)) + 60;
    const height = Math.max(32, ...nodes.map((node) => (node.y ?? 0) - minY)) + 60;
    if (shelfX && shelfX + width > shelfWidth) { shelfX = 0; shelfY += shelfHeight; shelfHeight = 0; }
    for (const node of nodes) { positions.set(node.id, { x: (node.x ?? 0) - minX + shelfX, y: (node.y ?? 0) - minY + shelfY }); }
    shelfX += width; shelfHeight = Math.max(shelfHeight, height);
  }
  return {
    positions, community, components,
    degree: new Map(ids.map((id) => [id, neighbours.get(id)?.size ?? 0])),
    unsupported: new Set(graph.statements.filter((node) => !index.producers.has(node.id)).map((node) => node.id)),
    unconsumed: new Set(graph.statements.filter((node) => !index.consumers.has(node.id)).map((node) => node.id)),
  };
}
