// Independent expected behavior for the public argument-forest browser journey.
// This model imports no production state, router, or corpus code.
import { createMachine, type AnyMachineSnapshot } from "xstate";
import { getAdjacencyMap, getShortestPaths } from "xstate/graph";

const events = ["SELECT", "EXPLORE_NEGATION", "RETURN", "RESET", "RELOAD"] as const;
export type ForestEvent = (typeof events)[number];
export type ForestState = "overview" | "selected" | "negation";
export type ForestStep = { event: ForestEvent; state: ForestState };
export type ForestPath = { name: string; steps: readonly ForestStep[] };

const model = createMachine({
  id: "forest-review",
  initial: "overview",
  states: {
    overview: { on: { SELECT: "selected", RELOAD: "overview" } },
    selected: {
      on: { EXPLORE_NEGATION: "negation", RESET: "overview", RELOAD: "selected" },
    },
    negation: {
      on: { RETURN: "selected", RESET: "overview", RELOAD: "negation" },
    },
  },
});

type Snapshot = { value: unknown };
type RawPath = {
  state: Snapshot;
  steps: readonly { event: { type: string }; state: Snapshot }[];
};
type Vertex = {
  state: Snapshot;
  transitions: Record<string, { event: { type: string }; state: Snapshot }>;
};

const options = {
  events: events.map((type) => ({ type })),
  filterEvents: (state: AnyMachineSnapshot, event: { type: string }) => state.can(event),
};

function toSteps(path: RawPath): ForestStep[] {
  return path.steps
    .filter(({ event }) => event.type !== "xstate.init")
    .map(({ event, state }) => ({
      event: event.type as ForestEvent,
      state: String(state.value) as ForestState,
    }));
}

const adjacency = getAdjacencyMap(model, options) as unknown as Record<string, Vertex>;

function transitionKey(source: string, event: string, target: string): string {
  return `${source} --${event}--> ${target}`;
}

export function forestPaths(): ForestPath[] {
  const shortest = new Map<string, ForestStep[]>();
  for (const path of getShortestPaths(model, options) as unknown as RawPath[]) {
    shortest.set(JSON.stringify(path.state), toSteps(path));
  }

  const generated = [...shortest.values()];
  const exercised = new Set<string>();
  for (const path of generated) {
    let source: ForestState = "overview";
    for (const step of path) {
      exercised.add(transitionKey(source, step.event, step.state));
      source = step.state;
    }
  }

  // Shortest paths reach states but miss self-loops and return/reset edges.
  for (const vertex of Object.values(adjacency)) {
    const source = String(vertex.state.value);
    const prefix = shortest.get(JSON.stringify(vertex.state));
    if (!prefix) { throw new Error(`No shortest path to ${source}`); }
    for (const transition of Object.values(vertex.transitions)) {
      const target = String(transition.state.value);
      const key = transitionKey(source, transition.event.type, target);
      if (!exercised.has(key)) {
        generated.push([...prefix, {
          event: transition.event.type as ForestEvent,
          state: target as ForestState,
        }]);
        exercised.add(key);
      }
    }
  }

  // Each browser path asserts every intermediate state, so its prefixes are redundant.
  const unique = new Map(generated
    .filter((path) => path.length > 0)
    .map((path) => [path.map((step) => step.event).join(" > "), path]));
  const paths = [...unique.entries()]
    .filter(([name]) => ![...unique.keys()].some((other) => other !== name && other.startsWith(`${name} > `)))
    .map(([name, steps]) => ({ name, steps }))
    .sort((a, b) => a.name.localeCompare(b.name));
  if (paths.length > 12) { throw new Error("Forest story exceeds its 12-path browser budget"); }

  const covered = new Set<string>();
  for (const path of paths) {
    let source: ForestState = "overview";
    for (const step of path.steps) {
      covered.add(transitionKey(source, step.event, step.state));
      source = step.state;
    }
  }
  for (const vertex of Object.values(adjacency)) {
    for (const transition of Object.values(vertex.transitions)) {
      const key = transitionKey(String(vertex.state.value), transition.event.type, String(transition.state.value));
      if (!covered.has(key)) { throw new Error(`Untested forest transition: ${key}`); }
    }
  }
  return paths;
}

export const forestCoverage = {
  states: Object.keys(adjacency).length,
  transitions: Object.values(adjacency).reduce((total, vertex) => total + Object.keys(vertex.transitions).length, 0),
  paths: forestPaths().length,
};

if (import.meta.main) {
  console.log(`FOREST-1: ${forestCoverage.states} states, ${forestCoverage.transitions} transitions, ${forestCoverage.paths} browser paths`);
  for (const path of forestPaths()) { console.log(`- ${path.name}`); }
}
