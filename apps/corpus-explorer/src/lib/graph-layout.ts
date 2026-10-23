/**
 * Small layered (Sugiyama-style) layout: premises below the inferences that
 * use them, conclusions above. Edges point from support to supported, so an
 * edge's target is placed on a higher layer than its source. Cycles, which the
 * corpus allows (invariant 11), are broken for layout only by ignoring DFS
 * back edges. Within a layer, nodes are ordered by a few barycenter sweeps.
 */

export type LayoutNode = { id: string; width: number; height: number };
export type LayoutEdge = { source: string; target: string };
/** `maxRowWidth` wraps a wide layer into several rows inside its band. */
export type LayoutOptions = { layerGap?: number; nodeGap?: number; rowGap?: number; maxRowWidth?: number };
export type Point = { x: number; y: number };

export function layeredLayout(
  nodes: LayoutNode[],
  edges: LayoutEdge[],
  { layerGap = 90, nodeGap = 36, rowGap = 28, maxRowWidth = 1800 }: LayoutOptions = {},
): Map<string, Point> {
  const ids = new Set(nodes.map((node) => node.id));
  const outgoing = new Map<string, string[]>(nodes.map((node) => [node.id, []]));
  for (const edge of edges) {
    if (ids.has(edge.source) && ids.has(edge.target) && edge.source !== edge.target) {
      outgoing.get(edge.source)?.push(edge.target);
    }
  }

  // Drop back edges (iterative DFS) to get an acyclic edge set.
  const state = new Map<string, 0 | 1 | 2>();
  const forward = new Map<string, string[]>(nodes.map((node) => [node.id, []]));
  for (const node of nodes) {
    if (state.get(node.id)) continue;
    const stack: Array<{ id: string; next: number }> = [{ id: node.id, next: 0 }];
    state.set(node.id, 1);
    while (stack.length) {
      const frame = stack[stack.length - 1];
      const targets = outgoing.get(frame.id) ?? [];
      if (frame.next >= targets.length) {
        state.set(frame.id, 2);
        stack.pop();
        continue;
      }
      const target = targets[frame.next];
      frame.next += 1;
      const targetState = state.get(target) ?? 0;
      if (targetState === 1) continue; // back edge
      forward.get(frame.id)?.push(target);
      if (targetState === 0) {
        state.set(target, 1);
        stack.push({ id: target, next: 0 });
      }
    }
  }

  // Longest-path layering from the sources (premises) upward.
  const indegree = new Map<string, number>(nodes.map((node) => [node.id, 0]));
  for (const targets of forward.values()) {
    for (const target of targets) indegree.set(target, (indegree.get(target) ?? 0) + 1);
  }
  const rank = new Map<string, number>(nodes.map((node) => [node.id, 0]));
  const queue = nodes.filter((node) => indegree.get(node.id) === 0).map((node) => node.id);
  for (let cursor = 0; cursor < queue.length; cursor += 1) {
    const id = queue[cursor];
    for (const target of forward.get(id) ?? []) {
      rank.set(target, Math.max(rank.get(target) ?? 0, (rank.get(id) ?? 0) + 1));
      indegree.set(target, (indegree.get(target) ?? 0) - 1);
      if (indegree.get(target) === 0) queue.push(target);
    }
  }
  // Pull each source up to just below its lowest consumer, so premises sit near
  // the step that uses them rather than all on the bottom layer.
  const hasIncoming = new Set([...forward.values()].flat());
  for (let cursor = queue.length - 1; cursor >= 0; cursor -= 1) {
    const id = queue[cursor];
    const targets = forward.get(id) ?? [];
    if (targets.length && !hasIncoming.has(id)) {
      rank.set(id, Math.min(...targets.map((target) => rank.get(target) ?? 0)) - 1);
    }
  }

  const maxRank = Math.max(0, ...rank.values());
  const layers: string[][] = Array.from({ length: maxRank + 1 }, () => []);
  for (const node of nodes) layers[rank.get(node.id) ?? 0].push(node.id);

  const neighbours = new Map<string, string[]>(nodes.map((node) => [node.id, []]));
  for (const [source, targets] of forward) {
    for (const target of targets) {
      neighbours.get(source)?.push(target);
      neighbours.get(target)?.push(source);
    }
  }
  const order = new Map<string, number>();
  const renumber = (layer: string[]) => layer.forEach((id, index) => order.set(id, index));
  layers.forEach(renumber);
  for (let sweep = 0; sweep < 4; sweep += 1) {
    const sequence = sweep % 2 === 0 ? layers.slice(1) : layers.slice(0, -1).reverse();
    for (const layer of sequence) {
      const layerRank = rank.get(layer[0]) ?? 0;
      const adjacentRank = sweep % 2 === 0 ? layerRank - 1 : layerRank + 1;
      const barycenter = new Map(
        layer.map((id) => {
          const adjacent = (neighbours.get(id) ?? []).filter((other) => rank.get(other) === adjacentRank);
          const value = adjacent.length
            ? adjacent.reduce((sum, other) => sum + (order.get(other) ?? 0), 0) / adjacent.length
            : (order.get(id) ?? 0);
          return [id, value];
        }),
      );
      layer.sort((left, right) => (barycenter.get(left) ?? 0) - (barycenter.get(right) ?? 0));
      renumber(layer);
    }
  }

  const size = new Map(nodes.map((node) => [node.id, node]));
  const positions = new Map<string, Point>();
  let y = 0;
  for (let layerIndex = maxRank; layerIndex >= 0; layerIndex -= 1) {
    const rows: string[][] = [];
    let rowWidth = 0;
    for (const id of layers[layerIndex]) {
      const width = size.get(id)?.width ?? 0;
      const current = rows[rows.length - 1];
      if (!current || (current.length && rowWidth + nodeGap + width > maxRowWidth)) {
        rows.push([id]);
        rowWidth = width;
      } else {
        current.push(id);
        rowWidth += nodeGap + width;
      }
    }
    rows.forEach((row, rowIndex) => {
      const height = Math.max(0, ...row.map((id) => size.get(id)?.height ?? 0));
      const width = row.reduce((sum, id) => sum + (size.get(id)?.width ?? 0), 0) + nodeGap * (row.length - 1);
      let x = -width / 2;
      for (const id of row) {
        const node = size.get(id) as LayoutNode;
        positions.set(id, { x, y: y + (height - node.height) / 2 });
        x += node.width + nodeGap;
      }
      y += height + (rowIndex === rows.length - 1 ? layerGap : rowGap);
    });
  }
  return positions;
}
