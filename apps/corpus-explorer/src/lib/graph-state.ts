import type { ClusterMode, GraphStatus } from "./proposition-graph";

/** All /graph view state; it round-trips through the URL so views can be shared. */
export type GraphView = "root" | "focus" | "all";
export type FocusDirection = "up" | "down" | "both";

export type GraphState = {
  view: GraphView;
  scope: "global" | "goal";
  obligation: string;
  pins: string[];
  kind: string;
  expanded: string[];
  returnView: string;
  viewport: string;
  /** Root-path view: the statement whose supporting paths are shown. */
  target: string;
  /** Focus view: the centre node (statement or inference ID). */
  node: string;
  hops: number;
  dir: FocusDirection;
  /** Full view: how statements are grouped, and which groups are expanded. */
  cluster: ClusterMode;
  open: string[];
  q: string;
  status: GraphStatus[];
  /** Every listed tag must be present (AND). */
  tags: string[];
  source: string;
  /** Remove non-matching statements instead of dimming them. */
  hide: boolean;
  /** Selected node shown in the detail panel. */
  sel: string;
  /** Argument whose statements and inference steps are highlighted. */
  arg: string;
};

type ReadableParams = {
  get(name: string): string | null;
  getAll(name: string): string[];
};

const views: GraphView[] = ["root", "focus", "all"];
const directions: FocusDirection[] = ["up", "down", "both"];
const clusterModes: ClusterMode[] = ["passage", "source", "namespace"];
const statuses: GraphStatus[] = [
  "proved",
  "transcription",
  "self-evident",
  "defended",
  "alternative",
  "objection",
  "open",
  "derived",
  "source-only",
];

export const MAX_HOPS = 6;

export const DEFAULT_STATE: GraphState = {
  view: "all",
  scope: "global",
  obligation: "",
  pins: [],
  kind: "",
  expanded: [],
  returnView: "",
  viewport: "",
  target: "",
  node: "",
  hops: 2,
  dir: "both",
  cluster: "passage",
  open: [],
  q: "",
  status: [],
  tags: [],
  source: "",
  hide: false,
  sel: "",
  arg: "",
};

function oneOf<T extends string>(value: string | null, allowed: readonly T[], fallback: T): T {
  return value && (allowed as readonly string[]).includes(value) ? (value as T) : fallback;
}

function list(params: ReadableParams, name: string) {
  return [...new Set(params.getAll(name).filter(Boolean))];
}

export function parseGraphState(params: ReadableParams): GraphState {
  const hops = Number.parseInt(params.get("hops") ?? "", 10);
  return {
    view: oneOf(params.get("view"), views, DEFAULT_STATE.view),
    scope: params.get("scope") === "goal" ? "goal" : "global",
    obligation: params.get("obligation") ?? "",
    pins: list(params, "pin"),
    kind: params.get("kind") ?? "",
    expanded: list(params, "expand"),
    returnView: params.get("return") ?? "",
    viewport: params.get("viewport") ?? "",
    target: params.get("target") ?? "",
    node: params.get("node") ?? "",
    hops: Number.isFinite(hops) ? Math.min(MAX_HOPS, Math.max(0, hops)) : DEFAULT_STATE.hops,
    dir: oneOf(params.get("dir"), directions, DEFAULT_STATE.dir),
    cluster: oneOf(params.get("cluster"), clusterModes, DEFAULT_STATE.cluster),
    open: list(params, "open"),
    q: params.get("q") ?? "",
    status: list(params, "status").filter((value): value is GraphStatus => (statuses as string[]).includes(value)),
    tags: list(params, "tag"),
    source: params.get("source") ?? "",
    hide: params.get("hide") === "1",
    sel: params.get("sel") ?? "",
    arg: params.get("arg") ?? "",
  };
}

/** Serializes only non-default values, in a stable order. */
export function serializeGraphState(state: GraphState): string {
  const params = new URLSearchParams();
  if (state.view !== DEFAULT_STATE.view) params.set("view", state.view);
  if (state.target) params.set("target", state.target);
  if (state.node) params.set("node", state.node);
  if (state.hops !== DEFAULT_STATE.hops) params.set("hops", String(state.hops));
  if (state.dir !== DEFAULT_STATE.dir) params.set("dir", state.dir);
  if (state.cluster !== DEFAULT_STATE.cluster) params.set("cluster", state.cluster);
  for (const value of state.open) params.append("open", value);
  if (state.q) params.set("q", state.q);
  for (const value of state.status) params.append("status", value);
  for (const value of state.tags) params.append("tag", value);
  if (state.source) params.set("source", state.source);
  if (state.hide) params.set("hide", "1");
  if (state.sel) params.set("sel", state.sel);
  if (state.arg) params.set("arg", state.arg);
  if (state.scope !== "global") params.set("scope", state.scope);
  if (state.obligation) params.set("obligation", state.obligation);
  for (const pin of state.pins) params.append("pin", pin);
  if (state.kind) params.set("kind", state.kind);
  for (const id of state.expanded) params.append("expand", id);
  if (state.returnView) params.set("return", state.returnView);
  if (state.viewport) params.set("viewport", state.viewport);
  return params.toString();
}

export function hasFilters(state: GraphState) {
  return Boolean(state.q.trim() || state.status.length || state.tags.length || state.source);
}

/** Finite viewport values only; malformed links fall back to fit-to-view. */
export function parseViewport(value: string) {
  const parts = value.split(",").map(Number);
  if (
    !value ||
    parts.length !== 3 ||
    parts.some((part) => !Number.isFinite(part)) ||
    parts[2] < 0.05 ||
    parts[2] > 1.6
  ) {
    return undefined;
  }
  return { x: parts[0], y: parts[1], zoom: parts[2] };
}
