import Link from "next/link";

import type { CorpusAttempt } from "@/lib/premise-dossier";
import { nameOf } from "@/lib/corpus";

export function DossierAttemptIndex({ attempts }: { attempts: CorpusAttempt[] }) {
  return (
    <section className="record-section" aria-labelledby="dossier-attempts">
      <h2 id="dossier-attempts" className="eyebrow">Attempt log</h2>
      {attempts.length ? <ol className="mt-4 grid gap-4">{attempts.map((attempt) => <li id={attempt.id} key={attempt.id}>
        <p className="text-sm">{attempt.date} · {attempt.kind} · {attempt.outcome}</p>
        <Link className="link-quiet font-mono text-xs break-all" href={`/attempts/${attempt.id}`}>{nameOf(attempt.id)} · Full attempt and evidence →</Link>
        <p className="mt-2 text-sm leading-6">{attempt.summary.length > 180 ? `${attempt.summary.slice(0, 180).trimEnd()}…` : attempt.summary}</p>
      </li>)}</ol> : <p className="mt-3">No attempt is recorded for this proposition.</p>}
    </section>
  );
}
