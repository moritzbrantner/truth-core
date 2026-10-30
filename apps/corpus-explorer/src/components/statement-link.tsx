import Link from "next/link";

import { StatementStateMark } from "@/components/state-mark";
import type { Corpus } from "@/lib/corpus";
import { findStatement } from "@/lib/corpus";
import { type FrontierReport, statementState } from "@/lib/site-state";

/** One statement in a list: its frontier state, paraphrase and ID. */
export function StatementLink({ corpus, report, id, note }: { corpus: Corpus; report: FrontierReport; id: string; note?: string }) {
  const statement = findStatement(corpus, id);
  return (
    <li>
      <div className="flex flex-wrap items-center gap-2">
        <StatementStateMark state={statementState(report, id)} />
        {note ? <span className="eyebrow">{note}</span> : null}
      </div>
      <Link className="mt-2 block font-serif text-xl leading-snug hover:text-[var(--accent)]" href={`/statements/${id}`}>
        {statement?.paraphrase ?? id}
      </Link>
      <Link className="link-quiet mt-2 inline-block text-xs" href={`/statements/${id}#structure`}>Inspect proposition structure →</Link>
      <p className="mt-1 font-mono text-xs break-all text-[var(--muted)]">{id}</p>
    </li>
  );
}
