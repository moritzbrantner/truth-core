"use client";

import Link from "next/link";
import { useState } from "react";
import type { NextStepsReport } from "@/lib/next-steps";

/** Traversal is navigation only: every status and edge comes from frontier JSON. */
export function NextWorkMap({ dag, routes, root }: Pick<NextStepsReport, "dag" | "routes" | "root">) {
  const [focus, setFocus] = useState(root?.statement_id ?? "");
  const [routeId, setRouteId] = useState(routes.find((route) => route.cheapest)?.argument_id ?? "");
  const statements = new Map(dag.statements.map((statement) => [statement.statement_id, statement]));
  const focusStatement = statements.get(focus);
  const proofs = dag.arguments.filter((argument) => argument.conclusion_statement_id === focus);
  const chosen = proofs.find((argument) => argument.argument_id === routeId) ?? proofs[0];
  return <section aria-labelledby="next-map-heading" className="my-8 rounded border border-[var(--line)] p-5">
    <h2 id="next-map-heading" className="font-serif text-2xl">Follow the argument DAG</h2>
    <p className="my-2 text-sm text-[var(--muted)]">Select a premise to follow its arguments. Shared propositions keep the same ID. Premises below → selected argument → proposition above. Established means its premises are settled; a conditional proof can still have open premises.</p>
    <button className="link-quiet text-sm" onClick={() => { setFocus(root?.statement_id ?? ""); setRouteId(routes.find((route) => route.cheapest)?.argument_id ?? ""); }}>Return to root</button>
    <div className="mt-4 border-l-4 border-[var(--accent)] pl-4">
      <p className="text-xs">{focusStatement?.established ? "Established" : "Not established"} · {focusStatement?.status}</p>
      <Link className="font-serif text-xl link-quiet" href={`/statements/${focus}`}>{focusStatement?.paraphrase ?? focus}</Link>
      <p className="mt-1 break-all font-mono text-xs">{focus}</p>
    </div>
    {proofs.length ? <>
      <label className="mt-4 block text-sm">Argument into this proposition
        <select aria-label="Argument into selected proposition" className="mt-1 block w-full rounded border border-[var(--line)] bg-[var(--paper)] p-2" value={chosen?.argument_id} onChange={(event) => setRouteId(event.target.value)}>
          {proofs.map((argument) => <option key={argument.argument_id} value={argument.argument_id}>{argument.argument_id}</option>)}
        </select>
      </label>
      {chosen ? <div className="mt-4">
        <p className="text-sm">{chosen.verified ? "Verified argument" : "No verified result"}{chosen.transcription ? " · transcription" : ""}; all premises below are required together.</p>
        <p className="mt-2 text-sm text-[var(--muted)]">{chosen.meaning}</p>
        <ul className="mt-4 grid gap-3 sm:grid-cols-2">
          {chosen.premise_statement_ids.map((sid) => {
            const statement = statements.get(sid);
            return <li key={sid} className="rounded border border-[var(--line)] p-3">
              <p className="text-xs">{statement?.established ? "Established" : "Open obligation"}{statement?.depth ? ` · ${statement.depth}` : ""}</p>
              <button className="mt-1 text-left font-serif text-lg hover:underline" onClick={() => setFocus(sid)}>{statement?.paraphrase ?? sid}</button>
              <p className="mt-1 break-all font-mono text-xs text-[var(--muted)]">{sid}</p>
              <Link className="link-quiet text-xs" href={`/dossiers/${sid}`}>Dossier</Link>
            </li>;
          })}
        </ul>
      </div> : null}
    </> : <p className="mt-4 text-sm">No incoming argument is recorded in this root dependency graph. <Link className="link-quiet" href={`/dossiers/${focus}`}>Inspect the premise dossier</Link>.</p>}
  </section>;
}
