import { forceCenter, forceCollide, forceLink, forceManyBody, forceSimulation, type SimulationNodeDatum } from "d3-force";
import { researchLinkedStatements, type PropositionGraph } from "./proposition-graph";
import type { Point } from "./graph-layout";
import { indexGraph } from "./graph-view";

export const NETWORK_TICKS = 180;
export type NetworkStructure = {
  positions: Map<string, Point>;
  community: Map<string, number>;
  degree: Map<string, number>;
  unsupported: Set<string>;
  unconsumed: Set<string>;
  /** Endpoints of recorded non-inferential relations. */
  researchLinked: Set<string>;
  /** Components of inference edges alone; research links never change this count. */
  components: string[][];
  /** Islands after adding non-inferential research links for layout only. */
  layoutComponents: string[][];
  layoutComponentCount: number;
};

/** Presentation only: corpus relations pull research-neighbouring inference
 * islands together without creating proof paths, changing structural leaves,
 * or contributing to closure. Sorted input and bounded stopped simulations
 * give reproducible positions. Compute on the whole corpus, never the filter.
 */
export function networkStructure(graph: PropositionGraph): NetworkStructure {
  const index = indexGraph(graph);
  const ids = [...graph.statements.map((node) => node.id), ...graph.inferences.map((node) => node.id)].sort();
  const proofNeighbours = new Map(ids.map((id) => [id, new Set<string>()]));
  const layoutNeighbours = new Map(ids.map((id) => [id, new Set<string>()]));
  type LayoutLink = { source: string; target: string; research: boolean };
  const layoutLinks: LayoutLink[] = [];
  const linkPairs = new Set<string>();
  const connect = (source: string, target: string, research = false) => {
    if (source === target || !proofNeighbours.has(source) || !proofNeighbours.has(target)) { return; }
    if (!research) {
      proofNeighbours.get(source)?.add(target);
      proofNeighbours.get(target)?.add(source);
    }
    layoutNeighbours.get(source)?.add(target);
    layoutNeighbours.get(target)?.add(source);
    const key = source < target ? `${source}\0${target}` : `${target}\0${source}`;
    if (!linkPairs.has(key)) {
      linkPairs.add(key);
      layoutLinks.push({ source, target, research });
    }
  };
  for (const inference of [...graph.inferences].sort((a, b) => a.id.localeCompare(b.id))) {
    for (const id of [...new Set([...inference.inputs, ...inference.assumptions])].sort()) { connect(id, inference.id); }
    connect(inference.id, inference.output);
  }
  for (const relation of [...graph.relations].sort((a, b) => a.id.localeCompare(b.id))) {
    connect(relation.subject, relation.object, true);
  }
  const connectedComponents = (neighbours: Map<string, Set<string>>) => {
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
    return components.sort((a, b) => b.length - a.length || a[0].localeCompare(b[0]));
  };
  const components = connectedComponents(proofNeighbours);
  const layoutComponents = connectedComponents(layoutNeighbours);
  // Deterministic label propagation uses only incident inference connectivity.
  const labels = new Map(ids.map((id, i) => [id, i]));
  for (let round = 0; round < 8; round += 1) {
    for (const id of ids) {
      const votes = new Map<number, number>();
      for (const other of proofNeighbours.get(id) ?? []) {
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
  const layoutComponentById = new Map(layoutComponents.flatMap((component, i) => component.map((id) => [id, i] as const)));
  const edgesByComponent = layoutComponents.map(() => [] as LayoutLink[]);
  for (const link of layoutLinks) {
    const group = layoutComponentById.get(link.source);
    if (group !== undefined) edgesByComponent[group].push(link);
  }
  // Pack disconnected components into shelves, preserving islands rather than
  // letting an unconstrained global charge scatter them into a vast canvas.
  let shelfX = 0; let shelfY = 0; let shelfHeight = 0;
  const shelfWidth = Math.max(1000, Math.sqrt(ids.length) * 72);
  for (const [index, component] of layoutComponents.entries()) {
    if (component.length === 1) {
      if (shelfX + 40 > shelfWidth) { shelfX = 0; shelfY += shelfHeight; shelfHeight = 0; }
      positions.set(component[0], { x: shelfX, y: shelfY });
      shelfX += 40; shelfHeight = Math.max(shelfHeight, 40);
      continue;
    }
    const nodes: Array<SimulationNodeDatum & { id: string }> = component.map((id) => ({ id }));
    const edges = edgesByComponent[index].map((link) => ({ ...link }));
    const simulation = forceSimulation(nodes).stop()
      .force("link", forceLink(edges)
        .id((node) => (node as SimulationNodeDatum & { id: string }).id)
        .distance((link) => (link as LayoutLink).research ? 72 : 35)
        .strength((link) => (link as LayoutLink).research ? 0.22 : 0.65))
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
    positions, community, components, layoutComponents,
    layoutComponentCount: layoutComponents.length,
    degree: new Map(ids.map((id) => [id, proofNeighbours.get(id)?.size ?? 0])),
    researchLinked: researchLinkedStatements(graph),
    unsupported: new Set(graph.statements.filter((node) => !index.producers.has(node.id)).map((node) => node.id)),
    unconsumed: new Set(graph.statements.filter((node) => !index.consumers.has(node.id)).map((node) => node.id)),
  };
}
