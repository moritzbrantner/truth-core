"use client";

import Link from "next/link";
import { useEffect, useRef } from "react";

import type { ForestTreeModel } from "@/lib/argument-forest";
import type { BeliefConflictReview } from "@/lib/belief-conflicts";
import styles from "../forest.module.css";

export function ConflictReview({
  model, proposedId, review, onRejectAndAccept, onAcceptAnyway, onCancel,
}: {
  model: ForestTreeModel;
  proposedId: string;
  review: BeliefConflictReview;
  onRejectAndAccept: (ids: readonly string[]) => void;
  onAcceptAnyway: () => void;
  onCancel: () => void;
}) {
  const heading = useRef<HTMLHeadingElement>(null);
  useEffect(() => { heading.current?.focus(); }, []);
  const unavoidable = review.repairs.length ?
    review.repairs[0].filter((id) => review.repairs.every((option) => option.includes(id))) : [];
  return <section className={styles.beliefReview} aria-label="Review incompatible beliefs">
    <h2 ref={heading} tabIndex={-1}>This new belief conflicts with saved beliefs</h2>
    <p>You proposed accepting <strong>{model.statements[proposedId]?.paraphrase ?? proposedId}</strong>.
      The following already accepted propositions form certified incompatible conjunctions with it.</p>
    <ul className={styles.certifiedCoreList}>
      {review.cores.map((core) => <li key={core.key}>
        <strong>{core.caseId}</strong><span>{core.profile}</span>
        <ul>{core.statementIds.map((id) => <li key={id}>
          {id === proposedId ? <strong>New: </strong> : null}
          {model.statements[id]?.paraphrase ?? id}
        </li>)}</ul>
        <span>Certified result: {core.resultIds.map((id, index) =>
          <span key={id}>{index > 0 ? ", " : ""}<Link href={"/results/" + id}>{id}</Link></span>)}</span>
      </li>)}
    </ul>
    <h3>Ways to accept the new proposition</h3>
    {review.cannotRepairByRejectingOldBeliefs ?
      <p>At least one certified core contains the new proposition without any removable prior belief. Rejecting old beliefs alone cannot resolve that conflict in its recorded profile.</p> :
      <>
        {unavoidable.length ? <p>Every displayed minimal repair rejects: {unavoidable.map((id) => model.statements[id]?.paraphrase ?? id).join("; ")}.</p> :
          <p>No one prior proposition must always be rejected. Choose a set below; each set removes every displayed conflict.</p>}
        <ol className={styles.repairOptions}>
          {review.repairs.map((option) => <li key={option.join("|")}>
            <div>{option.map((id) => <p key={id}>{model.statements[id]?.paraphrase ?? id}</p>)}</div>
            <button type="button" onClick={() => onRejectAndAccept(option)}>
              Reject {option.length} and accept new belief
            </button>
          </li>)}
        </ol>
        {review.truncated ? <p>These are bounded repair suggestions; additional minimal options may exist.</p> : null}
      </>}
    <p className={styles.warning}>Rejecting a saved belief here means withdrawing acceptance, not asserting its negation.
      Removing these recorded incompatible cores does not prove the remaining propositions jointly satisfiable.
      Every certificate applies only within its displayed semantic profile; the profiles need not all hold at once.</p>
    <div className={styles.reviewActions}>
      <button type="button" onClick={onCancel}>Keep my existing beliefs</button>
      <button type="button" onClick={onAcceptAnyway}>Accept anyway, retaining the conflict</button>
    </div>
  </section>;
}
