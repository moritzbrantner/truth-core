"use client";

import Link from "next/link";
import styles from "./proof-overlay.module.css";
import type { ProofExploration } from "@/lib/proof-exploration";
import { suggestIntermediateLemma } from "@/lib/proof-exploration";
import type { PropositionGraph } from "@/lib/proposition-graph";

export function ProofExplorationPanel({ graph, result, running, onCancel, onFocus }: {
  graph: PropositionGraph;
  result: ProofExploration | null;
  running: boolean;
  onCancel: () => void;
  onFocus: (id: string) => void;
}) {
  if (running) {
    return <div role="status">Exploring exact statement identities… <button className="graph-button" onClick={onCancel} type="button">Cancel exploration</button></div>;
  }
  if (!result) {
    return null;
  }
  const candidate = suggestIntermediateLemma(result);
  const statementLink = (id: string) => <button className="graph-button font-mono" onClick={() => onFocus(id)} type="button">{id}</button>;
  return (
    <section aria-label="Proof exploration results" className={`graph-detail ${styles.panel}`}>
      <p role="status">{result.status === "complete" ? "Exploration complete" : result.status === "cancelled" ? "Exploration cancelled; partial results" : "Budget exhausted; partial results"} · {result.visits} visits</p>
      <p>Forward: {result.establishedStatementIds.length} established facts, {result.forwardStatementIds.length - result.establishedStatementIds.length} proposed consequences. Backward: {result.backwardStatementIds.length} required statements.</p>
      <p>Junctions are proposed compositions. Recording a result requires Lean, premise binding, Comparator and NanoDa; source readings and empirical obligations remain separate.</p>
      <details open>
        <summary>Proposed exact-ID junctions ({result.joins.length})</summary>
        {result.joins.length ? <ul>{result.joins.map((join) => <li key={join.statementId}>
          {statementLink(join.statementId)} · proposed
          {result.branches.filter((branch) => branch.requiredStatementIds.includes(join.statementId)).map((branch) => <p key={JSON.stringify([branch.inferenceId, branch.contextAssumptionIds])}>For {branch.inferenceId} → {branch.output}, remaining AND requirements: {branch.remainingStatementIds.join(", ") || "none"}. This is one OR branch.</p>)}
          {join.argumentIds.length ? <ul>{join.argumentIds.map((id) => {
            const argument = graph.arguments.find((entry) => entry.id === id);
            return <li key={id}>{id}: {argument?.resultIds.map((resultId) => <Link href={`/results/${resultId}`} key={resultId}>{resultId}</Link>)}</li>;
          })}</ul> : <span> · already established in selected scope</span>}
        </li>)}</ul> : <p>No junction found within this exploration. This is unresolved, not a refutation.</p>}
      </details>
      <details>
        <summary>AND obligations and OR branches ({result.branches.length})</summary>
        <ul>{result.branches.map((branch) => <li key={JSON.stringify([branch.inferenceId, branch.contextAssumptionIds])}>
          {statementLink(branch.inferenceId)} → {statementLink(branch.output)}
          {branch.contextAssumptionIds.length ? <p>Within local context: {branch.contextAssumptionIds.join(", ")}.</p> : null}
          <p>All required: {branch.requiredStatementIds.length ? branch.requiredStatementIds.join(", ") : "none"}.</p>
          <p>Remaining on this branch: {branch.remainingStatementIds.length ? branch.remainingStatementIds.join(", ") : "none; composition still proposed"}.</p>
          {branch.scopedAssumptionIds.length ? <p>Local assumptions: {branch.scopedAssumptionIds.join(", ")}; discharged: {branch.dischargedStatementIds.join(", ") || "none"}. Local assumptions are never forward facts.</p> : null}
          <p>{branch.resultIds.length ? "Containing result: " : "Unverified inference; no containing result. "}{branch.resultIds.map((id) => <Link href={`/results/${id}`} key={id}>{id}</Link>)}</p>
        </li>)}</ul>
      </details>
      {candidate ? <details>
        <summary>Unverified intermediate lemma candidate</summary>
        <p>{candidate.wording}</p>
        <p>Formalization: {candidate.formalization}. Intended bridge from {candidate.intendedBridge.fromStatementIds.join(", ") || "no established facts"} to {candidate.target}.</p>
        <p>Missing premises: {candidate.missingPremiseIds.join(", ") || "no terminal premise identified; inspect circular or unverified branches"}.</p>
        <ul>{candidate.needs.map((need) => <li key={need}>{need}</li>)}</ul>
        <p>Provenance: {candidate.provenance.method}, {candidate.provenance.visits} visits; inferences {candidate.provenance.inferenceIds.join(", ") || "none"}.</p>
        <Link href="/candidates">Inspect the source-range research queue</Link>
      </details> : null}
    </section>
  );
}
