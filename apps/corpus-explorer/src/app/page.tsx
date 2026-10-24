import Link from "next/link";

import { DepthMark, ResultKindMark, StatementStateMark } from "@/components/state-mark";
import { findStatement, getCorpus } from "@/lib/corpus";
import { STAGE_CONCLUSIONS } from "@/lib/proposition-graph";
import { getPropositionGraph } from "@/lib/proposition-graph-data";
import {
  CLOSURE_DESCRIPTIONS,
  CLOSURE_LABELS,
  DEFAULT_ROOT_STATEMENT_ID,
  type ClosureReason,
  type FrontierItem,
  formatUtc,
  getBuildInfo,
  getFrontierReport,
  resultKind,
  rivals,
  statementState,
} from "@/lib/site-state";

const STAGE_TITLES: Record<number, string> = {
  1: "God exists",
  2: "The classical attributes",
  3: "Revelation is possible and recognizable",
  4: "Jesus' claims and the Resurrection",
  5: "Christ founded a visible Church",
  6: "That Church is the Catholic Church",
};

function Count({ label, value, note }: { label: string; value: number | string; note?: string }) {
  return (
    <div>
      <dt className="eyebrow">{label}</dt>
      <dd className="mt-1 font-serif text-4xl">{value}</dd>
      {note ? <dd className="mt-1 text-xs text-[var(--muted)]">{note}</dd> : null}
    </div>
  );
}

function PremiseRow({ item, stages }: { item: FrontierItem; stages: number[] }) {
  return (
    <li>
      <div className="flex flex-wrap items-center gap-2">
        <DepthMark depth={item.depth} />
        {stages.map((stage) => (
          <span className="eyebrow" key={stage}>
            Stage {stage}
          </span>
        ))}
        {item.transcription_only ? <span className="eyebrow">transcribed only</span> : null}
      </div>
      <Link className="mt-2 block font-serif text-xl leading-snug hover:text-[var(--accent)]" href={`/statements/${item.statement_id}`}>
        {item.paraphrase}
      </Link>
      <p className="mt-1 font-mono text-xs break-all text-[var(--muted)]">
        {item.statement_id} · {item.transitive_dependent_arguments.length} dependent arguments
        {item.stating_claims.length ? ` · stated by ${item.stating_claims.length} source claim${item.stating_claims.length === 1 ? "" : "s"}` : ""}
        {item.supporting_claims.length ? ` · supported by ${item.supporting_claims.length}` : ""}
        {item.objections.length ? ` · ${item.objections.length} objection${item.objections.length === 1 ? "" : "s"}` : ""}
      </p>
    </li>
  );
}

export default function StatePage() {
  const corpus = getCorpus();
  const report = getFrontierReport();
  const build = getBuildInfo();
  const graph = getPropositionGraph(corpus);
  const graphById = new Map(graph.statements.map((statement) => [statement.id, statement]));
  const root = findStatement(corpus, DEFAULT_ROOT_STATEMENT_ID);
  const rootState = statementState(report, DEFAULT_ROOT_STATEMENT_ID);

  const reaching = report.items.filter((item) => item.path_to_root);
  const reachingDepth = {
    bare: reaching.filter((item) => item.depth === "bare").length,
    sourced: reaching.filter((item) => item.depth === "sourced").length,
  };
  const stagesOf = (statementId: string) => graphById.get(statementId)?.stages ?? [];

  const stages = STAGE_CONCLUSIONS.map(({ stage, statementId }) => {
    const beneath = graph.statements.filter((statement) => statement.id === statementId || statement.stages.includes(stage));
    const open = reaching.filter((item) => item.statement_id === statementId || stagesOf(item.statement_id).includes(stage));
    const closed = beneath.filter((statement) => report.closed_statements[statement.id]);
    return {
      stage,
      statementId,
      statement: findStatement(corpus, statementId),
      state: statementState(report, statementId),
      open,
      bare: open.filter((item) => item.depth === "bare").length,
      closed: closed.length,
    };
  });
  const rootLevel = reaching.filter((item) => stagesOf(item.statement_id).length === 0);

  const rootArguments = corpus.arguments.filter((argument) => argument.conclusion_statement_id === DEFAULT_ROOT_STATEMENT_ID);
  const kinds = corpus.results.map((result) => resultKind(report, result.id));
  const derivations = kinds.filter((kind) => kind.kind === "derivation").length;
  const transcriptions = kinds.length - derivations;

  const onRootPath = new Set(graph.statements.filter((statement) => statement.stages.length).map((statement) => statement.id));
  onRootPath.add(DEFAULT_ROOT_STATEMENT_ID);
  for (const item of reaching) onRootPath.add(item.statement_id);
  const closedByReason: Partial<Record<ClosureReason, number>> = {};
  for (const [id, reason] of Object.entries(report.closed_statements)) {
    if (onRootPath.has(id)) closedByReason[reason] = (closedByReason[reason] ?? 0) + 1;
  }
  const provedOnPath = corpus.results
    .filter((result) => resultKind(report, result.id).kind === "derivation")
    .filter((result) => onRootPath.has(result.argument.conclusion_statement_id))
    .sort((a, b) => (stagesOf(a.argument.conclusion_statement_id)[0] ?? 9) - (stagesOf(b.argument.conclusion_statement_id)[0] ?? 9) || a.id.localeCompare(b.id));

  const { alternatives, objections } = rivals(corpus);
  const paraphrase = (id: string) => findStatement(corpus, id)?.paraphrase ?? id;
  const sortedReaching = [...reaching].sort((a, b) => (a.depth === b.depth ? 0 : a.depth === "bare" ? -1 : 1));

  return (
    <>
      <section className="grid gap-8 lg:grid-cols-[minmax(0,1fr)_19rem] lg:items-end">
        <div>
          <p className="eyebrow">The case for Catholicism · current state</p>
          <h1 className="mt-4 max-w-3xl font-serif text-5xl leading-[0.95] tracking-[-0.055em] sm:text-6xl">
            What is proved, and what is still open.
          </h1>
          <p className="mt-6 max-w-2xl text-lg leading-8 text-[var(--muted)]">
            Every path from the root should end in premises that are self-evident or whose alternatives are all refuted.
            Lean checks each step; the open premises below are what remains to be argued.
          </p>
          <p className="mt-4 text-sm text-[var(--muted)]">
            As of{" "}
            <a className="link-quiet font-mono" href={`${build.repositoryUrl}/commit/${build.commit}`} rel="noreferrer" target="_blank">
              main@{build.shortCommit}
            </a>
            {build.commitTime ? `, committed ${formatUtc(build.commitTime)}` : ""}. Rebuilt on every push to main.
          </p>
        </div>
        <dl className="grid grid-cols-2 gap-x-6 gap-y-5 border-l border-[var(--line)] pl-5">
          <Count label="Open premises" value={reaching.length} note={`${reachingDepth.bare} bare · ${reachingDepth.sourced} sourced`} />
          <Count
            label="Established"
            value={report.established_statements.length}
            note={`of ${Object.keys(report.closed_statements).length} closed statements`}
          />
          <Count label="Verified derivations" value={derivations} />
          <Count label="Transcriptions" value={transcriptions} note="verified, but close nothing alone" />
        </dl>
      </section>

      <aside className="mt-10 border-l-2 border-[var(--accent)] bg-[var(--callout)] px-5 py-5 text-sm leading-6 text-[var(--muted)]">
        <strong className="font-semibold text-[var(--ink)]">Three different kinds of record.</strong> A{" "}
        <em>verified derivation</em> is a Lean proof, checked by Comparator with no permitted axioms, that its conclusion
        follows from its premises. A <em>transcription</em> is also checked, but only restates a premise that already
        contains the conclusion. A <em>source reading</em> (claim) is a scholarly interpretation of a pinned passage; no
        machine checks it. Proof never makes a premise true: that is what the open premises are for.
      </aside>

      <section className="record-section">
        <p className="eyebrow">Root</p>
        <div className="mt-4 flex flex-wrap items-center gap-3">
          <StatementStateMark state={rootState} />
          <span className="font-mono text-xs text-[var(--muted)]">{DEFAULT_ROOT_STATEMENT_ID}</span>
        </div>
        <Link className="mt-3 block max-w-4xl font-serif text-3xl leading-tight tracking-[-0.03em] hover:text-[var(--accent)]" href={`/statements/${DEFAULT_ROOT_STATEMENT_ID}`}>
          {root?.paraphrase ?? "The root statement is not in the corpus yet."}
        </Link>
        <p className="mt-4 max-w-3xl text-sm leading-6 text-[var(--muted)]">
          {rootState.kind === "closed" && rootState.established
            ? "The root is established: every premise beneath it is closed."
            : `Lean verifies that the root follows from its premises, but ${reaching.length} open premises still reach it, so it is not established. Verified arguments that conclude the root:`}
        </p>
        {rootArguments.length ? (
          <ul className="mt-3 grid gap-2 text-sm text-[var(--muted)]">
            {rootArguments.map((argument) => {
              const result = corpus.results.find((entry) => entry.argument_id === argument.id);
              return (
                <li key={argument.id}>
                  {result ? (
                    <Link className="link-quiet font-mono text-xs" href={`/results/${result.id}`}>
                      {argument.id}
                    </Link>
                  ) : (
                    <span className="font-mono text-xs">{argument.id}</span>
                  )}{" "}
                  — {argument.premise_statement_ids.filter((premise) => !report.closed_statements[premise]).length} of{" "}
                  {argument.premise_statement_ids.length} premises open
                </li>
              );
            })}
          </ul>
        ) : null}
      </section>

      <section className="record-section">
        <p className="eyebrow">The six stages</p>
        <h2 className="mt-3 font-serif text-3xl tracking-[-0.03em]">Stage by stage</h2>
        <p className="mt-3 max-w-3xl text-sm leading-6 text-[var(--muted)]">
          A stage is established only when its conclusion and everything beneath it are closed. The bar shows closed
          statements against open premises among everything the stage rests on.
        </p>
        <div className="mt-6">
          {stages.map((stage) => {
            const total = stage.closed + stage.open.length;
            return (
              <div className="stage-row" key={stage.stage}>
                <span className="stage-number">{stage.stage}</span>
                <div>
                  <Link className="font-serif text-2xl leading-tight hover:text-[var(--accent)]" href={`/statements/${stage.statementId}`}>
                    {STAGE_TITLES[stage.stage]}
                  </Link>
                  <p className="mt-1 text-sm leading-6 text-[var(--muted)]">{stage.statement?.paraphrase}</p>
                </div>
                <div className="grid gap-2">
                  <StatementStateMark state={stage.state} />
                  <div aria-hidden="true" className="meter">
                    <span style={{ width: `${total ? (100 * stage.closed) / total : 0}%`, background: "var(--status-proved)" }} />
                    <span style={{ width: `${total ? (100 * (stage.open.length - stage.bare)) / total : 0}%`, background: "var(--status-open)" }} />
                    <span style={{ width: `${total ? (100 * stage.bare) / total : 0}%`, background: "var(--status-objection)" }} />
                  </div>
                </div>
                <p className="text-sm leading-6 text-[var(--muted)]">
                  <span className="text-[var(--ink)]">{stage.closed}</span> closed ·{" "}
                  <span className="text-[var(--ink)]">{stage.open.length}</span> open
                  {stage.bare ? ` (${stage.bare} bare)` : ""}
                </p>
              </div>
            );
          })}
          {rootLevel.length ? (
            <div className="stage-row">
              <span className="stage-number">+</span>
              <div>
                <p className="font-serif text-2xl leading-tight">Bridges to the root</p>
                <p className="mt-1 text-sm leading-6 text-[var(--muted)]">Premises of the root arguments outside the six stages.</p>
              </div>
              <div />
              <p className="text-sm leading-6 text-[var(--muted)]">
                <span className="text-[var(--ink)]">{rootLevel.length}</span> open
              </p>
            </div>
          ) : null}
        </div>
        <p className="mt-4 flex flex-wrap gap-4 text-xs text-[var(--muted)]">
          <span><span className="state-mark-dot" style={{ background: "var(--status-proved)" }} /> closed</span>
          <span><span className="state-mark-dot" style={{ background: "var(--status-open)" }} /> open, sourced</span>
          <span><span className="state-mark-dot" style={{ background: "var(--status-objection)" }} /> open, bare</span>
        </p>
      </section>

      <section className="record-section">
        <p className="eyebrow">The frontier</p>
        <h2 className="mt-3 font-serif text-3xl tracking-[-0.03em]">Open premises on the way to the root</h2>
        <p className="mt-3 max-w-3xl text-sm leading-6 text-[var(--muted)]">
          <strong className="text-[var(--ink)]">Bare</strong>: no source states or supports it.{" "}
          <strong className="text-[var(--ink)]">Sourced</strong>: a source states or supports it, but it is not yet defended.
          Bare premises come first; the project drives them to zero first. Same list as{" "}
          <code className="font-mono">corpus.py frontier --reaching-root</code>.
        </p>
        <ul className="premise-list mt-6">
          {sortedReaching.map((item) => (
            <PremiseRow item={item} key={item.statement_id} stages={stagesOf(item.statement_id)} />
          ))}
        </ul>
        <p className="mt-4 text-sm text-[var(--muted)]">
          {report.open_premise_count - reaching.length} further open premises do not reach the root.{" "}
          <Link className="link-quiet" href="/graph">
            Explore them in the graph
          </Link>
          .
        </p>
      </section>

      <section className="record-section">
        <p className="eyebrow">Closed</p>
        <h2 className="mt-3 font-serif text-3xl tracking-[-0.03em]">Closed on the root&apos;s paths</h2>
        <p className="mt-3 max-w-3xl text-sm leading-6 text-[var(--muted)]">
          A closed statement is off the frontier. It is <em>established</em> only when everything beneath it is closed too;
          most closed statements are still proved from open premises. Of the statements on the root&apos;s paths,{" "}
          {report.established_statements.filter((id) => onRootPath.has(id)).length} are established.
        </p>
        <dl className="mt-6 grid gap-x-8 gap-y-4 text-sm sm:grid-cols-2 lg:grid-cols-4">
          {(Object.keys(CLOSURE_LABELS) as ClosureReason[]).map((reason) => (
            <div key={reason}>
              <dt className="eyebrow">{CLOSURE_LABELS[reason]}</dt>
              <dd className="mt-1 font-serif text-3xl">{closedByReason[reason] ?? 0}</dd>
              <dd className="mt-1 text-xs leading-5 text-[var(--muted)]">{CLOSURE_DESCRIPTIONS[reason]}</dd>
            </div>
          ))}
        </dl>
        <div className="mt-8 grid gap-3">
          {provedOnPath.map((result) => (
            <Link className="record-link" href={`/results/${result.id}`} key={result.id}>
              <div className="flex flex-wrap items-center gap-2">
                <ResultKindMark kind={resultKind(report, result.id)} />
                {stagesOf(result.argument.conclusion_statement_id).slice(0, 1).map((stage) => (
                  <span className="eyebrow" key={stage}>
                    Stage {stage}
                  </span>
                ))}
              </div>
              <p className="mt-3 font-serif text-xl leading-snug">{paraphrase(result.argument.conclusion_statement_id)}</p>
              <p className="mt-2 font-mono text-xs text-[var(--muted)]">{result.id}</p>
            </Link>
          ))}
        </div>
      </section>

      <section className="record-section">
        <p className="eyebrow">Rivals and objections</p>
        <h2 className="mt-3 font-serif text-3xl tracking-[-0.03em]">Alternatives, refuted and not</h2>
        <div className="mt-6 grid gap-8 lg:grid-cols-2">
          <div>
            <p className="eyebrow">Recorded alternatives ({alternatives.length})</p>
            <ul className="premise-list mt-3">
              {alternatives.map((alternative) => (
                <li key={alternative.relationId}>
                  {alternative.refutedBy.length ? (
                    <span className="state-mark" data-tone="defended">
                      <span className="state-mark-dot" /> Refuted
                    </span>
                  ) : (
                    <span className="state-mark" data-tone="open">
                      <span className="state-mark-dot" /> Not yet refuted
                    </span>
                  )}
                  <Link className="mt-2 block font-serif text-lg leading-snug hover:text-[var(--accent)]" href={`/statements/${alternative.subject}`}>
                    {paraphrase(alternative.subject)}
                  </Link>
                  <p className="mt-1 text-xs text-[var(--muted)]">
                    alternative to{" "}
                    <Link className="link-quiet" href={`/statements/${alternative.target}`}>
                      {alternative.target}
                    </Link>
                    {alternative.refutedBy.map((argumentId) => {
                      const result = corpus.results.find((entry) => entry.argument_id === argumentId);
                      return result ? (
                        <span key={argumentId}>
                          {" "}
                          · refuted by{" "}
                          <Link className="link-quiet font-mono" href={`/results/${result.id}`}>
                            {argumentId}
                          </Link>
                        </span>
                      ) : null;
                    })}
                  </p>
                </li>
              ))}
            </ul>
          </div>
          <div>
            <p className="eyebrow">Recorded objections ({objections.length})</p>
            <ul className="premise-list mt-3">
              {objections.map((objection) => (
                <li key={objection.relationId}>
                  <span className="state-mark" data-tone="objection">
                    <span className="state-mark-dot" /> Attacks
                  </span>
                  {objection.subjectKind === "statement" ? (
                    <Link className="mt-2 block font-serif text-lg leading-snug hover:text-[var(--accent)]" href={`/statements/${objection.subject}`}>
                      {paraphrase(objection.subject)}
                    </Link>
                  ) : (
                    <p className="mt-2 font-mono text-sm">{objection.subject}</p>
                  )}
                  <p className="mt-1 text-xs text-[var(--muted)]">
                    against{" "}
                    <Link className="link-quiet" href={`/statements/${objection.target}`}>
                      {objection.target}
                    </Link>
                  </p>
                </li>
              ))}
            </ul>
          </div>
        </div>
      </section>
    </>
  );
}
