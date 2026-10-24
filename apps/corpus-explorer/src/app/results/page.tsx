import Link from "next/link";

import { ResultKindMark } from "@/components/state-mark";
import { findStatement, getCorpus } from "@/lib/corpus";
import { getFrontierReport, resultKind } from "@/lib/site-state";

export default function ResultsPage() {
  const corpus = getCorpus();
  const report = getFrontierReport();
  const results = corpus.results.map((result) => ({ result, kind: resultKind(report, result.id) }));
  const groups = [
    {
      title: "Verified derivations",
      note: "The conclusion is derived in Lean from the premises; the proof could have failed.",
      entries: results.filter((entry) => entry.kind.kind === "derivation"),
    },
    {
      title: "Transcriptions",
      note: "Checked, but the proof applies one premise that already contains the conclusion (invariant 16). They close nothing unless every premise is closed.",
      entries: results.filter((entry) => entry.kind.kind === "transcription"),
    },
  ];

  return (
    <section className="max-w-4xl">
      <p className="eyebrow">Formal consequence</p>
      <h1 className="mt-4 font-serif text-5xl tracking-[-0.05em] sm:text-6xl">Verified arguments</h1>
      <p className="mt-6 max-w-3xl text-lg leading-8 text-[var(--muted)]">
        Each result is a Lean theorem checked by Comparator against its frozen Challenge, with no permitted axioms. A result
        verifies consequence, not the truth of its premises or the fidelity of the underlying source readings.
      </p>
      {groups.map((group) => (
        <section className="record-section" key={group.title}>
          <p className="eyebrow">{group.entries.length} results</p>
          <h2 className="mt-3 font-serif text-3xl tracking-[-0.03em]">{group.title}</h2>
          <p className="mt-3 text-sm leading-6 text-[var(--muted)]">{group.note}</p>
          <div className="mt-6 grid gap-3">
            {group.entries.map(({ result, kind }) => (
              <Link className="record-link" href={`/results/${result.id}`} key={result.id}>
                <ResultKindMark kind={kind} />
                <p className="mt-3 font-serif text-xl leading-snug">
                  {findStatement(corpus, result.argument.conclusion_statement_id)?.paraphrase ?? result.meaning}
                </p>
                <p className="mt-2 font-mono text-xs text-[var(--muted)]">
                  {result.id} · {result.argument.premise_statement_ids.length} premises
                </p>
              </Link>
            ))}
          </div>
        </section>
      ))}
    </section>
  );
}
