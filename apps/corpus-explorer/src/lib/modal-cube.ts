export type AxiomId = "D" | "T" | "B" | "4" | "5";
export type FrameCondition = "serial" | "reflexive" | "symmetric" | "transitive" | "euclidean";
export type ModalSystemId =
  | "K"
  | "KB"
  | "K4"
  | "K5"
  | "K45"
  | "KD"
  | "KDB"
  | "KD4"
  | "KD5"
  | "KD45"
  | "KT"
  | "KTB"
  | "S4"
  | "KB5"
  | "S5";
export type WorldId = "actual" | "nearby" | "remote";

export type AxiomDefinition = {
  id: AxiomId;
  formula: string;
  condition: FrameCondition;
  explanation: string;
  leanTheorem: string;
};

export type ModalSystem = {
  id: ModalSystemId;
  name: string;
  explicitAxioms: AxiomId[];
  description: string;
  position: { x: number; y: number };
};

export type WorldEdge = {
  source: WorldId;
  target: WorldId;
};

export const AXIOMS: Record<AxiomId, AxiomDefinition> = {
  D: {
    id: "D",
    formula: "□p → ◇p",
    condition: "serial",
    explanation: "Every world has at least one accessible world.",
    leanTheorem: "TruthCore.Modal.axiomD_valid",
  },
  T: {
    id: "T",
    formula: "□p → p",
    condition: "reflexive",
    explanation: "Every world accesses itself. SEP calls this axiom M in its map.",
    leanTheorem: "TruthCore.Modal.axiomT_valid",
  },
  B: {
    id: "B",
    formula: "p → □◇p",
    condition: "symmetric",
    explanation: "If one world accesses another, the second can access the first.",
    leanTheorem: "TruthCore.Modal.axiomB_valid",
  },
  "4": {
    id: "4",
    formula: "□p → □□p",
    condition: "transitive",
    explanation: "Two accessibility steps can be collapsed into one.",
    leanTheorem: "TruthCore.Modal.axiom4_valid",
  },
  "5": {
    id: "5",
    formula: "◇p → □◇p",
    condition: "euclidean",
    explanation: "Worlds accessible from a common origin can access one another.",
    leanTheorem: "TruthCore.Modal.axiom5_valid",
  },
};

export const MODAL_SYSTEMS: ModalSystem[] = [
  { id: "K", name: "K", explicitAxioms: [], description: "All Kripke frames.", position: { x: 390, y: 660 } },
  { id: "KB", name: "KB", explicitAxioms: ["B"], description: "Symmetric frames.", position: { x: 40, y: 510 } },
  { id: "K4", name: "K4", explicitAxioms: ["4"], description: "Transitive frames.", position: { x: 260, y: 510 } },
  { id: "K5", name: "K5", explicitAxioms: ["5"], description: "Euclidean frames.", position: { x: 520, y: 510 } },
  { id: "KD", name: "KD", explicitAxioms: ["D"], description: "Serial frames.", position: { x: 760, y: 510 } },
  { id: "KB5", name: "KB5", explicitAxioms: ["B", "5"], description: "Symmetric + Euclidean; transitivity follows.", position: { x: 30, y: 170 } },
  { id: "K45", name: "K45", explicitAxioms: ["4", "5"], description: "Transitive + Euclidean frames.", position: { x: 250, y: 360 } },
  { id: "KDB", name: "KDB", explicitAxioms: ["D", "B"], description: "Serial + symmetric frames.", position: { x: 650, y: 360 } },
  { id: "KD4", name: "KD4", explicitAxioms: ["D", "4"], description: "Serial + transitive frames.", position: { x: 420, y: 360 } },
  { id: "KD5", name: "KD5", explicitAxioms: ["D", "5"], description: "Serial + Euclidean frames.", position: { x: 820, y: 360 } },
  { id: "KD45", name: "KD45", explicitAxioms: ["D", "4", "5"], description: "Serial + transitive + Euclidean frames.", position: { x: 610, y: 210 } },
  { id: "KT", name: "T", explicitAxioms: ["T"], description: "Reflexive frames; seriality follows.", position: { x: 880, y: 210 } },
  { id: "KTB", name: "TB", explicitAxioms: ["T", "B"], description: "Reflexive + symmetric frames.", position: { x: 770, y: 70 } },
  { id: "S4", name: "S4", explicitAxioms: ["T", "4"], description: "Reflexive + transitive frames.", position: { x: 430, y: 70 } },
  { id: "S5", name: "S5", explicitAxioms: ["T", "5"], description: "Reflexive + Euclidean; B, 4 and D follow.", position: { x: 600, y: -70 } },
];

/** Hasse edges are directed from weaker to stronger systems. */
export const MODAL_CUBE_EDGES: Array<[ModalSystemId, ModalSystemId]> = [
  ["K", "KB"],
  ["K", "K4"],
  ["K", "K5"],
  ["K", "KD"],
  ["KB", "KDB"],
  ["KB", "KB5"],
  ["K4", "K45"],
  ["K4", "KD4"],
  ["K5", "K45"],
  ["K5", "KD5"],
  ["K45", "KD45"],
  ["K45", "KB5"],
  ["KD", "KDB"],
  ["KD", "KD4"],
  ["KD", "KD5"],
  ["KD", "KT"],
  ["KDB", "KTB"],
  ["KD4", "KD45"],
  ["KD4", "S4"],
  ["KD5", "KD45"],
  ["KD45", "S5"],
  ["KT", "KTB"],
  ["KT", "S4"],
  ["KTB", "S5"],
  ["S4", "S5"],
  ["KB5", "S5"],
];

export const WORLDS: Array<{ id: WorldId; label: string; x: number; y: number }> = [
  { id: "actual", label: "Actual", x: 20, y: 170 },
  { id: "nearby", label: "Nearby", x: 260, y: 70 },
  { id: "remote", label: "Remote", x: 500, y: 170 },
];

const CONDITION_FOR_AXIOM: Record<AxiomId, FrameCondition> = {
  D: "serial",
  T: "reflexive",
  B: "symmetric",
  "4": "transitive",
  "5": "euclidean",
};

export function closeAxioms(input: Iterable<AxiomId>): Set<AxiomId> {
  const result = new Set(input);
  let changed = true;

  while (changed) {
    changed = false;
    const add = (axiom: AxiomId) => {
      if (!result.has(axiom)) {
        result.add(axiom);
        changed = true;
      }
    };

    if (result.has("T")) add("D");
    if (result.has("B") && result.has("4")) add("5");
    if (result.has("B") && result.has("5")) add("4");
    if (result.has("T") && result.has("5")) {
      add("B");
      add("4");
    }
  }

  return result;
}

export function impliedAxioms(system: ModalSystem): Set<AxiomId> {
  return closeAxioms(system.explicitAxioms);
}

export function requiredConditions(system: ModalSystem): Set<FrameCondition> {
  return new Set([...impliedAxioms(system)].map((axiom) => CONDITION_FOR_AXIOM[axiom]));
}

function edgeKey(source: WorldId, target: WorldId) {
  return `${source}:${target}`;
}

function parseEdge(key: string): WorldEdge {
  const [source, target] = key.split(":") as [WorldId, WorldId];
  return { source, target };
}

/**
 * Build a small witness frame by closing a simple directed chain under the
 * conditions required by the selected modal system. A witness may satisfy
 * extra conditions accidentally; the UI reports those separately.
 */
export function buildWitnessFrame(system: ModalSystem): WorldEdge[] {
  const conditions = requiredConditions(system);
  const edges = new Set<string>([edgeKey("actual", "nearby"), edgeKey("nearby", "remote")]);
  let changed = true;

  const add = (source: WorldId, target: WorldId) => {
    const key = edgeKey(source, target);
    if (edges.has(key)) return false;
    edges.add(key);
    return true;
  };

  while (changed) {
    changed = false;

    if (conditions.has("serial")) {
      for (const world of WORLDS) {
        const hasSuccessor = [...edges].some((key) => key.startsWith(`${world.id}:`));
        if (!hasSuccessor) changed = add(world.id, world.id) || changed;
      }
    }

    if (conditions.has("reflexive")) {
      for (const world of WORLDS) changed = add(world.id, world.id) || changed;
    }

    const snapshot = [...edges].map(parseEdge);
    if (conditions.has("symmetric")) {
      for (const edge of snapshot) changed = add(edge.target, edge.source) || changed;
    }

    if (conditions.has("transitive")) {
      for (const first of snapshot) {
        for (const second of snapshot) {
          if (first.target === second.source) {
            changed = add(first.source, second.target) || changed;
          }
        }
      }
    }

    if (conditions.has("euclidean")) {
      for (const left of snapshot) {
        for (const right of snapshot) {
          if (left.source === right.source) {
            changed = add(left.target, right.target) || changed;
          }
        }
      }
    }
  }

  return [...edges].map(parseEdge).sort((a, b) => edgeKey(a.source, a.target).localeCompare(edgeKey(b.source, b.target)));
}

export function detectFrameConditions(edges: WorldEdge[]): Set<FrameCondition> {
  const has = (source: WorldId, target: WorldId) =>
    edges.some((edge) => edge.source === source && edge.target === target);
  const worlds = WORLDS.map((world) => world.id);
  const conditions = new Set<FrameCondition>();

  if (worlds.every((world) => worlds.some((next) => has(world, next)))) conditions.add("serial");
  if (worlds.every((world) => has(world, world))) conditions.add("reflexive");
  if (edges.every((edge) => has(edge.target, edge.source))) conditions.add("symmetric");

  const transitive = edges.every((first) =>
    edges.every((second) => first.target !== second.source || has(first.source, second.target)),
  );
  if (transitive) conditions.add("transitive");

  const euclidean = edges.every((left) =>
    edges.every((right) => left.source !== right.source || has(left.target, right.target)),
  );
  if (euclidean) conditions.add("euclidean");

  return conditions;
}

export function modalTruthAt(
  world: WorldId,
  edges: WorldEdge[],
  valuation: Record<WorldId, boolean>,
) {
  const accessible = edges.filter((edge) => edge.source === world).map((edge) => edge.target);
  return {
    p: valuation[world],
    possibleP: accessible.some((next) => valuation[next]),
    necessaryP: accessible.every((next) => valuation[next]),
    accessible,
  };
}
