import Link from "next/link";
import { notFound } from "next/navigation";

import { ResultKindMark, StatementStateMark } from "@/components/state-mark";
import { StatementLink } from "@/components/statement-link";
import {
  argumentsConcludingStatement,
  argumentsUsingStatement,
  claimsForStatement,
  findClaim,
  findSource,
  findStatement,
  getCorpus,
  resultsForArgument,
} from "@/lib/corpus";
import { leanIndex } from "@/lib/lean-source";
import { CLOSURE_DESCRIPTIONS, getFrontierReport, resultKind, sourceUrl, statementState } from "@/lib/site-state";

type StatementPageProps = {
  params: Promise<{ statementId: string }>;
};

export function generateStaticParams() {
  return getCorpus().statements.map((statement) => ({ statementId: statement.id }));
}

export default async function StatementPage({ params }: StatementPageProps) {
  const { statementId } = await params;
  const corpus = getCorpus();
  const statement = findStatement(corpus, statementId);
  if (!statement) {
    notFound();
  }
  const report = getFrontierReport();
  const state = statementState(report, statement.id);
  const lean = statement.lean_declaration ? leanIndex().get(statement.lean_declaration) : undefined;
  const claims = claimsForStatement(corpus, statement.id);
  const concluding = argumentsConcludingStatement(corpus, statement.id);
  const using = argumentsUsingStatement(corpus, statement.id);
  const relations = corpus.relations.filter((relation) => relation.object_id === statement.id || relation.subject_id === statement.id);
  const supports = relations.filter((relation) => relation.predicate === "supports" && relation.object_id === statement.id);
  const closure = report.closed_via_transcription.find((entry) => entry.statement_id === statement.id);
  const describe = (id: string) => findStatement(corpus, id)?.paraphrase ?? findClaim(corpus, id)?.paraphrase ?? id;

  return (
    <article className="max-w-5xl">
      <Link className="link-quiet text-sm" href="/">
        ← State of the case
      </Link>
      <div className="mt-10 flex flex-wrap items-center gap-3">
        <StatementStateMark state={state} />
        <p className="font-mono text-xs break-all text-[var(--muted)]">{statement.id}</p>
      </div>
      <h1 className="mt-5 font-serif text-4xl leading-[1.02] tracking-[-0.04em] sm:text-5xl">{statement.paraphrase}</h1>

      <section className="record-section">
        <p className="eyebrow">Where it stands</p>
        {state.kind === "closed" ? (
          <p className="mt-3 text-lg leading-8">
            {CLOSURE_DESCRIPTIONS[state.reason]}{" "}
            {state.established
              ? "It is established: it rests only on self-evident or defended statements, through verified results."
              : "It is not established yet: every verified route to it still passes through open premises."}
          </p>
        ) : state.kind === "open" ? (
          <div className="mt-3 grid gap-3 text-lg leading-8">
            <p>
              An open premise.{" "}
              {state.item.depth === "bare"
                ? "It is bare: no source claim states it and no source supports it."
                : "It is sourced but not yet defended: it is not proved, not marked self-evident, and its alternatives are not all refuted."}
              {state.item.transcription_only ? " It is the conclusion of a transcription whose premises are not all closed, which does not close it." : ""}
            </p>
            <p className="text-sm text-[var(--muted)]">
              {state.item.transitive_dependent_arguments.length} arguments depend on it, directly or indirectly.
            </p>
            {state.item.path_to_root ? (
              <p className="text-sm leading-7 text-[var(--muted)]">
                Path to the root:{" "}
                {state.item.path_to_root.map((step, index) => (
                  <span key={`${step}-${index}`}>
                    {index ? " → " : ""}
                    {step.startsWith("STMT-") ? (
                      <Link className="link-quiet font-mono text-xs" href={`/statements/${step}`}>
                        {step}
                      </Link>
                    ) : (
                      <span className="font-mono text-xs">{step}</span>
                    )}
                  </span>
                ))}
              </p>
            ) : (
              <p className="text-sm text-[var(--muted)]">It does not reach the root.</p>
            )}
          </div>
        ) : (
          <p className="mt-3 text-lg leading-8 text-[var(--muted)]">
            No argument uses this statement as a premise, so it is not on the frontier.
          </p>
        )}
        {statement.self_evident ? (
          <div className="mt-4 text-sm leading-6">
            <p className="eyebrow">Self-evidence rests on</p>
            <ul className="mt-2 grid gap-1">
              {statement.self_evident.justification_ids.map((id) => (
                <li key={id}>
                  <Link className="link-quiet font-mono text-xs" href={findClaim(corpus, id) ? `/claims/${id}` : `/results/${id}`}>
                    {id}
                  </Link>{" "}
                  <span className="text-[var(--muted)]">{describe(id)}</span>
                </li>
              ))}
            </ul>
          </div>
        ) : null}
        {closure ? (
          <p className="mt-4 text-sm leading-6 text-[var(--muted)]">
            Carried by transcription{" "}
            <Link className="link-quiet font-mono text-xs" href={`/results/${closure.result_id}`}>
              {closure.result_id}
            </Link>{" "}
            from closed premises {closure.premise_statement_ids.join(", ")}.
          </p>
        ) : null}
      </section>

      <section className="record-section">
        <p className="eyebrow">Established by</p>
        {concluding.length ? (
          <div className="mt-4 grid gap-3">
            {concluding.map((argument) => {
              const results = resultsForArgument(corpus, argument.id);
              return results.length ? (
                results.map((result) => (
                  <Link className="record-link" href={`/results/${result.id}`} key={result.id}>
                    <ResultKindMark kind={resultKind(report, result.id)} />
                    <p className="mt-3 text-sm leading-6 text-[var(--muted)]">{argument.meaning}</p>
                    <p className="mt-2 font-mono text-xs text-[var(--muted)]">
                      {result.id} · {argument.premise_statement_ids.length} premises
                    </p>
                  </Link>
                ))
              ) : (
                <div className="record-link" key={argument.id}>
                  <span className="eyebrow">Argument without a result</span>
                  <p className="mt-3 text-sm leading-6 text-[var(--muted)]">{argument.meaning}</p>
                  <p className="mt-2 font-mono text-xs text-[var(--muted)]">{argument.id}</p>
                </div>
              );
            })}
          </div>
        ) : (
          <p className="mt-3 text-sm text-[var(--muted)]">No argument concludes this statement.</p>
        )}
      </section>

      <section className="record-section">
        <p className="eyebrow">Source witnesses</p>
        {claims.length || supports.length ? (
          <div className="mt-4 divide-y divide-[var(--line)] border-y border-[var(--line)]">
            {claims.map((claim) => {
              const source = findSource(corpus, claim.source_id);
              return (
                <Link className="block py-4 transition hover:text-[var(--accent)]" href={`/claims/${claim.id}`} key={claim.id}>
                  <span className="eyebrow">States it{claim.basis === "translation" ? " · read from a translation" : ""}</span>
                  <span className="mt-1 block font-serif text-lg">
                    {source ? `${source.author}, ${source.work}` : claim.source_id} · {claim.locator}
                  </span>
                  <span className="mt-1 block text-sm leading-6 text-[var(--muted)]">{claim.interpretation}</span>
                  <span className="mt-1 block font-mono text-xs text-[var(--muted)]">
                    {claim.id} · passage {claim.passage.id}
                  </span>
                </Link>
              );
            })}
            {supports.map((relation) => (
              <Link className="block py-4 transition hover:text-[var(--accent)]" href={`/claims/${relation.subject_id}`} key={relation.id}>
                <span className="eyebrow">Supports it (evidence, not an inference)</span>
                <span className="mt-1 block font-serif text-lg">{describe(relation.subject_id)}</span>
                <span className="mt-1 block font-mono text-xs text-[var(--muted)]">{relation.subject_id}</span>
              </Link>
            ))}
          </div>
        ) : (
          <p className="mt-3 text-sm text-[var(--muted)]">No source claim states or supports this statement.</p>
        )}
        <p className="mt-3 text-xs leading-5 text-[var(--muted)]">
          A pinned witness fixes which text was consulted. Whether the reading is faithful remains a scholarly judgment.
        </p>
      </section>

      <section className="record-section">
        <p className="eyebrow">Used by</p>
        {using.length ? (
          <div className="mt-4 grid gap-3">
            {using.map((argument) => {
              const results = resultsForArgument(corpus, argument.id);
              const conclusion = findStatement(corpus, argument.conclusion_statement_id);
              return (
                <Link
                  className="record-link"
                  href={results.length ? `/results/${results[0].id}` : `/statements/${argument.conclusion_statement_id}`}
                  key={argument.id}
                >
                  <div className="flex flex-wrap items-center gap-2">
                    {results.length ? <ResultKindMark kind={resultKind(report, results[0].id)} /> : <span className="eyebrow">No result</span>}
                    <span className="eyebrow">premise of {argument.id}</span>
                  </div>
                  <p className="mt-3 font-serif text-xl leading-snug">⇒ {conclusion?.paraphrase ?? argument.conclusion_statement_id}</p>
                </Link>
              );
            })}
          </div>
        ) : (
          <p className="mt-3 text-sm text-[var(--muted)]">No argument uses this statement as a premise.</p>
        )}
      </section>

      {relations.filter((relation) => relation.predicate !== "supports").length ? (
        <section className="record-section">
          <p className="eyebrow">Alternatives, objections and other relations</p>
          <ul className="premise-list mt-3">
            {relations
              .filter((relation) => relation.predicate !== "supports")
              .map((relation) => {
                const other = relation.subject_id === statement.id ? relation.object_id : relation.subject_id;
                const otherIsStatement = Boolean(findStatement(corpus, other));
                const phrase =
                  relation.subject_id === statement.id
                    ? `this ${relation.predicate.replaceAll("_", " ")}`
                    : `${relation.predicate.replaceAll("_", " ")} this`;
                return otherIsStatement ? (
                  <StatementLink corpus={corpus} id={other} key={relation.id} note={phrase} report={report} />
                ) : (
                  <li key={relation.id}>
                    <span className="eyebrow">{phrase}</span>
                    <p className="mt-2 font-mono text-sm">{other}</p>
                  </li>
                );
              })}
          </ul>
        </section>
      ) : null}

      <section className="record-section">
        <p className="eyebrow">Lean declaration</p>
        {statement.lean_declaration ? (
          <>
            <p className="mt-3 font-mono text-sm break-all">{statement.lean_declaration}</p>
            {lean ? (
              <>
                <pre className="lean-snippet">{lean.snippet}</pre>
                <a className="link-quiet mt-2 inline-block text-sm" href={sourceUrl(lean.file, lean.line)} rel="noreferrer" target="_blank">
                  {lean.file}:{lean.line} ↗
                </a>
              </>
            ) : null}
          </>
        ) : (
          <p className="mt-3 text-sm text-[var(--muted)]">No Lean declaration is recorded for this statement.</p>
        )}
      </section>
    </article>
  );
}
