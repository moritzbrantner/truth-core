import Link from "next/link";
import { notFound } from "next/navigation";

import { ArgumentFlow } from "@/components/argument-flow";
import { StrengthComparisons } from "@/components/strength-comparisons";
import { comparisonsForResult, getStrengthComparisons } from "@/lib/strength-comparisons";
import { ResultKindMark, StatementStateMark } from "@/components/state-mark";
import { StatementLink } from "@/components/statement-link";
import { TermsSection } from "@/components/terms-section";
import { claimsForResult, comparatorForResult, findResult, findStatement, getCorpus } from "@/lib/corpus";
import { forkUses } from "@/lib/fork-use";
import { theoremInModule } from "@/lib/lean-source";
import { TRANSCRIPTION_KIND_DESCRIPTIONS, getFrontierReport, resultKind, sourceUrl, statementState } from "@/lib/site-state";

type ResultPageProps = {
  params: Promise<{ resultId: string }>;
};

export function generateStaticParams() {
  return getCorpus().results.map((result) => ({ resultId: result.id }));
}

export default async function ResultPage({ params }: ResultPageProps) {
  const { resultId } = await params;
  const corpus = getCorpus();
  const result = findResult(corpus, resultId);

  if (!result) {
    notFound();
  }

  const report = getFrontierReport();
  const kind = resultKind(report, result.id);
  const claims = claimsForResult(corpus, result.id);
  const comparator = comparatorForResult(result);
  const challenge = theoremInModule(result.challenge_module, result.theorem);
  const solution = theoremInModule(result.solution_module, result.theorem);
  const argument = result.argument;
  const conclusion = findStatement(corpus, argument.conclusion_statement_id);
  const openPremises = argument.premise_statement_ids.filter((premise) => !report.closed_statements[premise]);
  // Ship only the arguments this one can expand into (those concluding its
  // premises, transitively), not the whole corpus, to keep each page small.
  const reachable = new Map([[argument.id, argument]]);
  for (const current of reachable.values()) {
    for (const candidate of corpus.arguments) {
      if (!reachable.has(candidate.id) && current.premise_statement_ids.includes(candidate.conclusion_statement_id)) {
        reachable.set(candidate.id, candidate);
      }
    }
  }
  const projectionArguments = [...reachable.values()];
  const inferenceIds = new Set(projectionArguments.flatMap((entry) => entry.inference_ids));
  const projectionInferences = corpus.inferences.filter((inference) => inferenceIds.has(inference.id));
  const statementIds = new Set([
    ...projectionArguments.flatMap((entry) => [...entry.premise_statement_ids, entry.conclusion_statement_id]),
    ...projectionInferences.flatMap((inference) => [...inference.input_statement_ids, inference.output_statement_id]),
  ]);
  const projectionCorpus = {
    statements: corpus.statements.filter((statement) => statementIds.has(statement.id)).map(({ id, paraphrase }) => ({ id, paraphrase })),
    inferences: projectionInferences,
    arguments: projectionArguments,
    verified_argument_ids: corpus.results.map((entry) => entry.argument_id).filter((id) => reachable.has(id)),
  };
  const appliedForks = forkUses(corpus, result);
  const heuristic = kind.flag && kind.kind === "derivation";

  return (
    <article className="max-w-6xl">
      <Link className="link-quiet text-sm" href="/results">
        ← All verified arguments
      </Link>
      <div className="mt-10 flex flex-wrap items-center gap-3">
        <ResultKindMark kind={kind} />
        <p className="font-mono text-xs break-all text-[var(--muted)]">{result.id}</p>
      </div>
      <h1 className="mt-5 max-w-4xl font-serif text-4xl leading-[1.02] tracking-[-0.04em] sm:text-5xl">
        {conclusion?.paraphrase ?? argument.conclusion_statement_id}
      </h1>
      <p className="mt-6 max-w-4xl text-lg leading-8 text-[var(--muted)]">{result.meaning}</p>

      <StrengthComparisons comparisons={comparisonsForResult(getStrengthComparisons(), result.id)} />

      <aside className="mt-10 max-w-4xl border-l-2 border-[var(--accent)] bg-[var(--callout)] px-5 py-5 text-sm leading-6 text-[var(--muted)]">
        {kind.kind === "transcription" ? (
          <>
            <strong className="font-semibold text-[var(--ink)]">A transcription, not a proof.</strong>{" "}
            {kind.transcription?.declared
              ? `The result record declares it (${kind.transcription.kind}): ${TRANSCRIPTION_KIND_DESCRIPTIONS[kind.transcription.kind]}`
              : kind.flag?.single_application_of
                ? `The Lean proof applies the single hypothesis ${kind.flag.single_application_of}, which already contains the conclusion.`
                : `The Lean proof only assembles the hypotheses ${(kind.flag?.assembly_of ?? []).join(", ")}.`}{" "}
            It maps the source&apos;s &ldquo;therefore&rdquo; faithfully, and it closes its conclusion only if every premise is
            closed (AGENTS.md invariant 16).
          </>
        ) : (
          <>
            <strong className="font-semibold text-[var(--ink)]">Formal consequence only.</strong> This result verifies that the
            conclusion follows from the premises below. It does not make those premises true or confirm a source reading.
            {heuristic
              ? ` Heuristic note: the proof has ${kind.flag?.proof_steps} step${kind.flag?.proof_steps === 1 ? "" : "s"}${
                  kind.flag?.goal_consequent_premises.length ? " and a premise whose consequent is the goal" : ""
                }, so check that the premises carry no more than the source says.`
              : ""}
          </>
        )}
      </aside>

      <section className="record-section max-w-4xl">
        <p className="eyebrow">Conclusion</p>
        <div className="mt-3 flex flex-wrap items-center gap-3">
          <StatementStateMark state={statementState(report, argument.conclusion_statement_id)} />
          <Link className="link-quiet font-mono text-xs" href={`/statements/${argument.conclusion_statement_id}`}>
            {argument.conclusion_statement_id}
          </Link>
        </div>
      </section>

      <section className="record-section max-w-4xl">
        <p className="eyebrow">
          Premises · {argument.premise_statement_ids.length} total · {openPremises.length} open
        </p>
        {argument.premise_statement_ids.length ? (
          <ul className="premise-list mt-3">
            {argument.premise_statement_ids.map((premise) => (
              <StatementLink corpus={corpus} id={premise} key={premise} report={report} />
            ))}
          </ul>
        ) : (
          <p className="mt-3 text-sm text-[var(--muted)]">None: the conclusion is a theorem of logic.</p>
        )}
        {argument.commitment_statement_ids?.length ? (
          <>
            <p className="eyebrow mt-8">Commitments shown jointly consistent</p>
            <ul className="premise-list mt-3">
              {argument.commitment_statement_ids.map((id) => (
                <StatementLink corpus={corpus} id={id} key={id} report={report} />
              ))}
            </ul>
          </>
        ) : null}
      </section>

      <div className="max-w-4xl">
        <TermsSection
          corpus={corpus}
          records={[
            argument,
            ...[argument.conclusion_statement_id, ...argument.premise_statement_ids, ...(argument.commitment_statement_ids ?? [])].flatMap(
              (id) => findStatement(corpus, id) ?? [],
            ),
          ]}
          title="Terms and senses the derivation depends on"
        />
      </div>

      <section className="record-section max-w-4xl">
        <p className="eyebrow">Lean</p>
        <h2 className="mt-3 font-serif text-3xl tracking-[-0.03em]">The advertised theorem</h2>
        <p className="mt-3 text-sm leading-6 text-[var(--muted)]">
          As frozen in the Challenge module (with <code className="font-mono">sorry</code>). The Solution module proves the same
          statement; Comparator checks that the two agree and that the proof uses only the permitted axioms.
        </p>
        {challenge ? <pre className="lean-snippet">{challenge.snippet}</pre> : null}
        <p className="mt-3 flex flex-wrap gap-4 text-sm">
          {challenge ? (
            <a className="link-quiet" href={sourceUrl(challenge.file, challenge.line)} rel="noreferrer" target="_blank">
              Challenge ↗
            </a>
          ) : null}
          {solution ? (
            <a className="link-quiet" href={sourceUrl(solution.file, solution.line)} rel="noreferrer" target="_blank">
              Solution (proof) ↗
            </a>
          ) : null}
          <a className="link-quiet" href={sourceUrl(result.comparator_config)} rel="noreferrer" target="_blank">
            Comparator config ↗
          </a>
        </p>
        <dl className="mt-6 grid gap-4 text-sm sm:grid-cols-[11rem_minmax(0,1fr)]">
          <dt className="text-[var(--muted)]">Theorem</dt>
          <dd className="font-mono break-all">{result.theorem}</dd>
          <dt className="text-[var(--muted)]">Permitted axioms</dt>
          <dd>{comparator.permitted_axioms.length ? comparator.permitted_axioms.join(", ") : "None"}</dd>
          <dt className="text-[var(--muted)]">NanoDa kernel check</dt>
          <dd>{comparator.enable_nanoda ? "Enabled" : "Disabled"}</dd>
          {comparator.theorem_names && comparator.theorem_names.length > 1 ? (
            <>
              <dt className="text-[var(--muted)]">Also checked</dt>
              <dd className="font-mono break-all">
                {comparator.theorem_names.filter((name) => name !== result.theorem).join(", ")}
              </dd>
            </>
          ) : null}
          <dt className="text-[var(--muted)]">Gate</dt>
          <dd>Comparator, NanoDa and the premise binding check run on every change before it merges to main.</dd>
        </dl>
      </section>

      {appliedForks.length ? (
        <section aria-label="Fork applied here" className="record-section max-w-4xl">
          <p className="eyebrow">Fork applied here</p>
          <h2 className="mt-3 font-serif text-3xl tracking-[-0.03em]">Certified case-split inputs</h2>
          <p className="mt-3 text-sm leading-6 text-[var(--muted)]">
            These declared disjunction-elimination steps consume the exact result inputs below.
            Follow the coverage result to inspect its theorem, background and branch scope;
            the advertised theorem above binds this use and its remaining premises.
          </p>
          {appliedForks.map(({ step, evidence }) => (
            <div className="mt-6 border-l-2 border-[var(--accent)] pl-4" key={step.id}>
              <p className="font-mono text-xs break-all">{step.id}</p>
              <p className="mt-3 text-sm leading-6">{step.meaning}</p>
              <ul className="mt-4 space-y-3">
                {evidence.map((producer) => (
                  <li key={producer.id}>
                    <Link className="link-quiet font-mono text-xs break-all" href={`/results/${producer.id}`}>
                      {producer.id}
                    </Link>
                    <p className="mt-1 font-mono text-xs break-all text-[var(--muted)]">{producer.theorem}</p>
                    <p className="mt-1 text-sm text-[var(--muted)]">
                      Advertised premises: {producer.argument.premise_statement_ids.length
                        ? producer.argument.premise_statement_ids.join(", ")
                        : "none; inspect the theorem’s explicit quantified background"}.
                    </p>
                  </li>
                ))}
              </ul>
              <p className="mt-4 text-sm">
                Branch consequence: <Link className="link-quiet font-mono text-xs break-all" href={`/statements/${step.output_statement_id}`}>
                  {step.output_statement_id}
                </Link>
              </p>
            </div>
          ))}
        </section>
      ) : null}

      <section className="record-section">
        <p className="eyebrow">Argument composition</p>
        <h2 className="mt-3 font-serif text-3xl tracking-[-0.03em]">Proof projection</h2>
        <p className="mt-3 max-w-3xl text-sm leading-6 text-[var(--muted)]">
          Each argument is a reusable block. Expand a block to inspect its premises and inference steps.
        </p>
        <div className="mt-6">
          <ArgumentFlow corpus={projectionCorpus} rootArgumentId={result.argument_id} />
        </div>
      </section>

      {claims.length ? (
        <section className="record-section max-w-4xl">
          <p className="eyebrow">Source readings of the premises</p>
          <div className="mt-4 divide-y divide-[var(--line)] border-y border-[var(--line)]">
            {claims.map((claim) => (
              <Link className="block py-5 transition hover:text-[var(--accent)]" href={`/claims/${claim.id}`} key={claim.id}>
                <p className="font-serif text-xl leading-tight">{claim.paraphrase}</p>
                <p className="mt-2 font-mono text-xs text-[var(--muted)]">
                  {claim.id} · {claim.locator}
                </p>
              </Link>
            ))}
          </div>
        </section>
      ) : null}
    </article>
  );
}
