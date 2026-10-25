"use client";

import Link from "next/link";
import type { GraphState } from "@/lib/graph-state";
import type { ResearchObligation } from "@/lib/research-frontier";

type Props = {
  items: ResearchObligation[];
  selected?: ResearchObligation;
  state: GraphState;
  select: (item: ResearchObligation) => void;
  update: (patch: Partial<GraphState> | ((current: GraphState) => Partial<GraphState>)) => void;
};

export function ResearchQueue({ items, selected, state, select, update }: Props) {
  const related = items.filter((item) => item.statementIds.includes(state.sel));
  return (
    <aside className="research-queue" aria-label="Research obligations">
      <div className="flex items-center justify-between gap-2">
        <h3 className="font-serif text-xl">Research frontier</h3>
        <span aria-live="polite">{items.length} obligations</span>
      </div>
      <label className="field-label mt-3">
        Obligation type
        <select className="field-control" value={state.kind} onChange={(event) => update({ kind: event.target.value })}>
          <option value="">Knowledge and exploration</option>
          {["derivation", "evidence", "alternative", "objection", "interpretation", "exploration"].map((kind) => (
            <option key={kind} value={kind}>
              {kind}
            </option>
          ))}
        </select>
      </label>
      <p className="mt-2 text-xs text-[var(--muted)]">
        Pinned first, then root reachability and dependent argument count; selected-node relevance breaks ties. No
        effort or certainty estimate is inferred.
      </p>
      {state.sel ? (
        <p className="mt-2 text-sm" role="status">
          {related.length} related to selected node
        </p>
      ) : null}
      <ol className="research-items mt-3">
        {items.map((item) => (
          <li
            key={item.id}
            data-related={item.statementIds.includes(state.sel)}
            data-selected={state.obligation === item.id}
          >
            <button
              className="research-select"
              type="button"
              onClick={() => select(item)}
              aria-pressed={state.obligation === item.id}
            >
              <span className="text-xs text-[var(--muted)]">
                {item.frontier} · {item.kind} · {item.dependents} dependents
                {item.rootRelevant ? " · root path" : ""}
              </span>
              <span className="block text-sm">{item.title}</span>
            </button>
            <button
              className="graph-link-button text-xs"
              type="button"
              aria-pressed={state.pins.includes(item.id)}
              onClick={() =>
                update((current) => ({
                  pins: current.pins.includes(item.id)
                    ? current.pins.filter((id) => id !== item.id)
                    : [...current.pins, item.id],
                }))
              }
            >
              {state.pins.includes(item.id) ? "Unpin obligation" : "Pin obligation"}
            </button>
          </li>
        ))}
      </ol>
      {!items.length ? (
        <p className="mt-3 text-sm">
          No recorded obligations in this scope. Return to global or choose another goal. Missing records do not prove
          completeness.
        </p>
      ) : null}
      {selected ? (
        <section className="research-blocker mt-4" aria-label="Selected obligation">
          <h4 className="font-semibold">
            {selected.kind}: {selected.title}
          </h4>
          <p className="mt-2 text-sm">{selected.blocker}</p>
          <p className="mt-2 text-sm">
            <strong>Next action:</strong> {selected.nextAction}
          </p>
          <p className="mt-2 font-mono text-xs break-all">
            {selected.recordIds.join(", ") || selected.statementIds.join(", ")}
          </p>
          {selected.href ? (
            <Link className="link-quiet mt-2 inline-block text-sm" href={selected.href}>
              Inspect corpus record →
            </Link>
          ) : null}
        </section>
      ) : null}
      <Link className="link-quiet mt-3 inline-block text-sm" href="/candidates">
        Source-range candidates →
      </Link>
    </aside>
  );
}
