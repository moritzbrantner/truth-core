import { parseGraphState, serializeGraphState, type GraphState } from "./graph-state";

/** URL bookmarks stay shallow: an overview and at most one supporting proof. */
function bookmark(state: GraphState) {
  return serializeGraphState({ ...state, returnView: "", supportView: "" });
}

export function traceSupport(state: GraphState, statementId: string): GraphState {
  return {
    ...state,
    view: "focus",
    layout: "layered",
    dir: "down",
    hops: 1,
    node: statementId,
    sel: statementId,
    viewport: "",
    returnView: state.returnView || bookmark(state),
    supportView: "",
  };
}

export function inspectDispute(state: GraphState, statementId: string): GraphState {
  return {
    ...state,
    view: "dispute",
    layout: "network",
    node: statementId,
    sel: statementId,
    viewport: "",
    returnView: state.returnView || bookmark(state),
    supportView: state.view === "focus" && state.dir === "down" ? bookmark(state) : state.supportView,
  };
}

export function restoreSupport(state: GraphState): GraphState | null {
  if (!state.supportView) return null;
  const previous = parseGraphState(new URLSearchParams(state.supportView));
  if (previous.view !== "focus" || previous.dir !== "down" || !previous.node) return null;
  return { ...previous, returnView: state.returnView, supportView: "" };
}

export function restoreOverview(state: GraphState): GraphState {
  const previous = parseGraphState(new URLSearchParams(state.returnView));
  return { ...previous, returnView: "", supportView: "" };
}
