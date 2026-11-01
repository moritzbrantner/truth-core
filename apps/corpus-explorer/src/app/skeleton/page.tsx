import Link from "next/link";

import { DepthMark, ResultKindMark } from "@/components/state-mark";
import { findStatement, getCorpus } from "@/lib/corpus";
import { getPropositionGraph } from "@/lib/proposition-graph-data";
import { researchFrontier } from "@/lib/research-frontier";
import { getFrontierReport, resultKind } from "@/lib/site-state";

import { skeletonProgress } from "./progress";

const connectionLabels = {
  discharged: "Discharged · established",
  connected: "Connected · conditional proof",
  transcribed: "Transcribed · premises remain",
  recorded: "Recorded · no separate checked result",
};

export default function SkeletonPage() {
  const corpus = getCorpus();
  const report = getFrontierReport();
  const research = researchFrontier(corpus, getPropositionGraph(corpus), report);
  const progress = skeletonProgress(corpus, report, research);
  const paraphrase = (id: string) => findStatement(corpus, id)?.paraphrase ?? id;
  const bare = progress.obligations.filter(({ item }) => item.depth === "bare").length;
  const explore = (id: string) => `/graph?${new URLSearchParams({ target: id, sel: id, scope: "goal", explore: "1" })}`;

  return (
    <>
      <header>
        <h1 className="font-serif text-4xl tracking-[-0.04em]">Skeleton progress</h1>
        <p className="mt-3 text-lg leading-7">
          {progress.obligations.length} open premises · {bare} bare · {progress.obligations.length - bare} sourced
        </p>
        <p className="mt-2 text-sm text-[var(--muted)]">
          {progress.discharged ? "Root discharged from established premises." : "Root not discharged. A connection proves consequence; it does not establish its open premises."}
        </p>
        <Link className="link-quiet mt-3 inline-block" href={`/statements/${progress.root}`}>
          {paraphrase(progress.root)}
        </Link>
      </header>

      <section aria-labelledby="connections-title" className="record-section">
        <h2 className="font-serif text-3xl tracking-[-0.03em]" id="connections-title">Checked connections</h2>
        {progress.routes.length === 0 ? (
          <p className="mt-3 text-sm text-[var(--muted)]">No root route is designated. <Link className="link-quiet" href={`/statements/${progress.root}`}>Inspect the root arguments</Link>.</p>
        ) : progress.routes.map(({ argument, results, connections }) => (
          <div className="mt-4" key={argument.id}>
            <details className="border-y border-[var(--line)] py-3 text-sm">
              <summary className="cursor-pointer">Designated root route <span className="font-mono break-all">{argument.id}</span></summary>
              <p className="mt-3 leading-6 text-[var(--muted)]">{argument.meaning}</p>
              <p className="mt-2">{argument.premise_statement_ids.length} listed premises. Other root arguments are alternatives; they are not blended into this route.</p>
              {results.map((result) => <p className="mt-2" key={result.id}><Link className="link-quiet font-mono break-all" href={`/results/${result.id}`}>{result.id}</Link></p>)}
            </details>
            <ol className="mt-3 divide-y divide-[var(--line)]">
              {connections.map(({ inference, results: supports, status, open }, index) => (
                <li className="py-5" key={inference.id}>
                  <div className="flex flex-wrap items-center gap-3">
                    <span className="eyebrow">Step {index + 1}</span>
                    <span className="state-mark" data-tone={status === "discharged" ? "proved" : "conditional"}>
                      <span aria-hidden="true" className="state-mark-dot" />{connectionLabels[status]}
                    </span>
                  </div>
                  <h3 className="mt-3 font-serif text-2xl leading-snug"><Link className="hover:text-[var(--accent)]" href={`/statements/${inference.output_statement_id}`}>{paraphrase(inference.output_statement_id)}</Link></h3>
                  <p className="mt-2 text-sm leading-6 text-[var(--muted)]">{inference.meaning}</p>
                  <p className="mt-2 text-sm">{open.length} open {open.length === 1 ? "premise remains" : "premises remain"} beneath this conclusion on the designated route.</p>
                  <details className="mt-3 text-sm">
                    <summary className="cursor-pointer text-[var(--accent)]">Inputs and supporting results</summary>
                    <ul className="mt-3 grid gap-2">
                      {inference.input_statement_ids.map((id) => <li key={id}><Link className="link-quiet" href={`/statements/${id}`}>{paraphrase(id)}</Link></li>)}
                    </ul>
                    {inference.assumption_statement_ids.length > 0 ? <p className="mt-3">Scoped assumptions: {inference.assumption_statement_ids.join(", ")}. Discharged locally: {inference.discharged_statement_ids.join(", ") || "none"}.</p> : null}
                    <h4 className="mt-4 font-semibold">Existing results</h4>
                    {supports.length ? <ul className="mt-2 grid gap-3">{supports.map((result) => (
                      <li key={result.id}>
                        <ResultKindMark kind={resultKind(report, result.id)} />
                        <Link className="link-quiet mt-1 block font-mono text-xs break-all" href={`/results/${result.id}`}>{result.id}</Link>
                        <p className="mt-1 text-[var(--muted)]">{result.argument.premise_statement_ids.length} explicit premises · theorem <span className="font-mono break-all">{result.theorem}</span></p>
                      </li>
                    ))}</ul> : <p className="mt-2 text-[var(--muted)]">This is a recorded step inside the root argument, without a separately bound result for this output.</p>}
                  </details>
                  <Link className="link-quiet mt-3 inline-block text-sm" href={explore(inference.output_statement_id)}>Explore this inference</Link>
                </li>
              ))}
            </ol>
          </div>
        ))}
      </section>

      <section aria-labelledby="obligations-title" className="record-section">
        <h2 className="font-serif text-3xl tracking-[-0.03em]" id="obligations-title">Root obligations</h2>
        <p className="mt-3 text-sm text-[var(--muted)]">Sourced means a reading states or supports a premise, not that the premise is discharged. Open a premise to see its next recorded gap.</p>
        <ol className="mt-5 divide-y divide-[var(--line)]">
          {progress.obligations.map(({ item, candidates }) => (
            <li className="py-4" key={item.statement_id}>
              <details id={`obligation-${item.statement_id}`}>
                <summary className="cursor-pointer leading-7">
                  <span className="mr-3 inline-block"><DepthMark depth={item.depth} /></span>
                  {item.paraphrase}
                </summary>
                <p className="mt-3 font-mono text-xs break-all text-[var(--muted)]">{item.statement_id}</p>
                <h3 className="mt-4 text-sm font-semibold">{candidates.length ? "Next recorded gap" : "Next inference not recorded"}</h3>
                {candidates.length ? <ul className="mt-2 grid gap-4 text-sm leading-6 [overflow-wrap:anywhere]">{candidates.map((candidate) => (
                  <li key={candidate.id}>
                    <p>{candidate.title}</p>
                    <p className="mt-1 text-[var(--muted)]">{candidate.blocker}</p>
                    {candidate.href ? <Link className="link-quiet mt-1 inline-block" href={candidate.href}>Read queued source and interpretation notes</Link> : null}
                  </li>
                ))}</ul> : <p className="mt-2 text-sm leading-6 text-[var(--muted)]">No queued candidate explicitly names this premise. A derivation establishing this exact statement is still missing; the graph offers research leads, not a proposed proof.</p>}
                <div className="mt-4 flex flex-wrap gap-4 text-sm">
                  <Link className="link-quiet" href={`/statements/${item.statement_id}`}>Premise and source readings</Link>
                  <Link className="link-quiet" href={explore(item.statement_id)}>Explore missing inference</Link>
                </div>
              </details>
            </li>
          ))}
        </ol>
      </section>
    </>
  );
}
