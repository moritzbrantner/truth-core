"use client";

import styles from "./proof-overlay.module.css";
import type { PropositionGraph } from "@/lib/proposition-graph";
import type { ProofSearchState } from "@/lib/proof-exploration-state";

export function ProofExplorationControls({ graph, target, state, start, hide }: {
  graph: PropositionGraph;
  target: string;
  state: ProofSearchState;
  start: (next: ProofSearchState & { target: string }) => void;
  hide: () => void;
}) {
  return <details open={state.explore}>
    <summary>Proof exploration</summary>
    <form className="graph-toolbar" onSubmit={(event) => {
      event.preventDefault();
      const data = new FormData(event.currentTarget);
      const budget = Number(data.get("budget"));
      const goal = String(data.get("goal") ?? "");
      if (!Number.isFinite(budget) || budget < 1 || budget > 10000 || !Number.isInteger(budget) || !graph.statements.some((s) => s.id === goal)) {
        return;
      }
      start({ explore: true, proofBudget: budget, proofScope: [...new Set(String(data.get("scope") ?? "").split(",").map((id) => id.trim()).filter(Boolean))].sort(), target: goal });
    }}>
      <label className="field-label">Proof goal
        <select className="field-control" defaultValue={target} key={target} name="goal" required>
          {graph.statements.map((statement) => <option key={statement.id} value={statement.id}>{statement.id}</option>)}
        </select>
      </label>
      <label className="field-label">Exploration budget (visits)
        <input className="field-control" defaultValue={state.proofBudget} key={state.proofBudget} max={10000} min={1} name="budget" required step={1} type="number" />
      </label>
      <label className="field-label">Available facts (statement IDs; blank uses all established facts)
        <input className="field-control" defaultValue={state.proofScope.join(", ")} key={state.proofScope.join(",")} name="scope" />
      </label>
      <button className="graph-button" type="submit">Explore proof</button>
      {state.explore ? <button className="graph-button" onClick={hide} type="button">Hide proof exploration</button> : null}
    </form>
    {state.explore ? <p className={styles.legend}><span className={styles.forward}>Forward established/proposed</span><span className={styles.backward}>Backward required</span><span className={styles.junction}>Proposed junction</span><span className={styles.blocker}>Remaining blocker</span></p> : null}
  </details>;
}
