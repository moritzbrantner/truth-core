"use client";

import Link from "next/link";
import { useState } from "react";

export type ProgressEntry = { id: string; title: string; search: string; established: boolean; hasComparison: boolean };
export function ProgressSearch({ entries }: { entries: ProgressEntry[] }) {
  const [query, setQuery] = useState("");
  const [status, setStatus] = useState("all");
  const matches = entries.filter((entry) => entry.search.toLowerCase().includes(query.toLowerCase()) && (status === "all" || entry.established === (status === "established")));
  return <section className="record-section">
    <label className="block">Find proposition, argument or sense<input className="mt-2 block w-full rounded border p-2" value={query} onChange={(event) => setQuery(event.target.value)} /></label>
    <label className="mt-3 block">Closure <select value={status} onChange={(event) => setStatus(event.target.value)}><option value="all">All</option><option value="established">Established</option><option value="open">Not established</option></select></label>
    <p className="mt-3">{matches.length} matching propositions</p>
    <ul className="mt-4 space-y-3">{matches.slice(0, 100).map((entry) => <li key={entry.id}><Link className="link-quiet" href={`/dossiers/${entry.id}#research-comparison`}>{entry.title}</Link> · {entry.established ? "established" : "not established"}</li>)}</ul>
    {matches.length > 100 ? <p>First 100 matches; narrow the search.</p> : null}
  </section>;
}
