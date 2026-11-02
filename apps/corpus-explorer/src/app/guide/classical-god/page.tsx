import type { Metadata } from "next";
import Link from "next/link";

import { StatementStateMark } from "@/components/state-mark";
import { getCorpus } from "@/lib/corpus";
import { theoremInModule } from "@/lib/lean-source";
import { getFrontierReport, sourceUrl, statementState, type FrontierReport } from "@/lib/site-state";
import { ASSEMBLY_RESULT_ID, buildGodWalkthrough, GOD_ROOT_ID, type GuideStage } from "./walkthrough";
import styles from "./walkthrough.module.css";

export const metadata: Metadata = {
  title: "From necessary being to classical God — Truth Core",
  description: "A guided, evidence-linked reading of Truth Core's conditional necessary-root and classical-God argument.",
};

function Stage({ stage, number, count, report }: {
  stage: GuideStage;
  number: number;
  count: number;
  report: FrontierReport;
}) {
  const proof = theoremInModule(stage.result.solution_module, stage.result.theorem);
  return <section id={`step-${number}`} className={styles.stage} aria-labelledby={`step-${number}-title`}>
    <div className={styles.stageHeading}>
      <span className={styles.stepNumber} aria-hidden="true">{String(number).padStart(2, "0")}</span>
      <div>
        <p className="eyebrow">Step {number} of {count} · {stage.transcription ? "Lean-checked assembly" : "Conditional derivation"}</p>
        <h2 id={`step-${number}-title`}>{stage.title}</h2>
      </div>
    </div>
    <div className={styles.stageBody}>
      <div className={styles.stageNarrative}>
        <p>{stage.explanation}</p>
        <div className={styles.conclusion}>
          <p className="eyebrow">Exact conclusion in the corpus</p>
          <Link href={`/statements/${stage.conclusion.id}`}>{stage.conclusion.paraphrase}</Link>
        </div>
        <p className={styles.nextQuestion}><strong>What is still needed?</strong> {stage.next}</p>
        <div className={styles.evidenceLinks}>
          <Link href={`/results/${stage.result.id}#proof-projection`}>Argument tree</Link>
          <Link href={`/results/${stage.result.id}#lean-evidence`}>Exact theorem and proof checks</Link>
          {proof ? <a href={sourceUrl(proof.file, proof.line)} target="_blank" rel="noreferrer">Lean solution ↗</a> : null}
        </div>
      </div>
      <aside className={styles.assumptions} aria-label={`Key premises for step ${number}`}>
        <h3>Questions this step depends on</h3>
        {number > 1 ? <p className={styles.supplied}>
          <Link href={`#step-${number - 1}`}>Uses the previous step&apos;s conclusion</Link> as one named input.
        </p> : null}
        <ul>
          {stage.focus.map((item) => <li key={item.statement.id}>
            <Link className={styles.focusTitle} href={`/statements/${item.statement.id}`}>{item.label}</Link>
            <p>{item.question}</p>
            <Link className={styles.dossierLink} href={`/dossiers/${item.statement.id}#dossier-instances`}>
              Source, rivals and countermodel status
            </Link>
          </li>)}
        </ul>
      </aside>
    </div>
    <details className={styles.technical}>
      <summary>Technical evidence · all {stage.premises.length} named inputs, sources and theorem</summary>
      <div className={styles.technicalInner}>
        <p>
          These are the exact direct inputs of <Link href={`/results/${stage.result.id}`}>{stage.result.id}</Link>.
          They are not all independent philosophical primitives. The status labels come from the corpus frontier,
          not from this walkthrough; a formally derived input can still rest on open premises.
        </p>
        <ol className={styles.premiseList}>
          {stage.premises.map((input) => <li key={input.statement.id}>
            <StatementStateMark state={statementState(report, input.statement.id)} />
            {input.fromPreviousStep ? <span className={styles.inputRole}>Supplied by previous step</span> : null}
            {input.onOpenRoute ? <span className={styles.inputRole}>Open on this root route</span> : null}
            <Link href={`/statements/${input.statement.id}`}>{input.statement.paraphrase}</Link>
            <Link className={styles.dossierLink} href={`/dossiers/${input.statement.id}`}>Premise dossier</Link>
          </li>)}
        </ol>
        <p className={styles.theoremName}>Lean: {stage.result.theorem}</p>
        {stage.sourceClaims.length ? <div className={styles.sourceRecords}>
          <h4>Selected existing source readings</h4>
          <ul>{stage.sourceClaims.map((claim) => <li key={claim.id}>
            <Link href={`/claims/${claim.id}`}>{claim.id}</Link> · {claim.locator}
          </li>)}</ul>
          <p>Source attribution records an interpretation, not a proof of the premise.</p>
        </div> : <p>No attributed source reading is attached to the highlighted inputs; consult each premise dossier.</p>}
        <details className={styles.corpusWording}>
          <summary>Full registered result description</summary>
          <p>{stage.result.description ?? stage.result.meaning}</p>
        </details>
      </div>
    </details>
    <div className={styles.stagePaging}>
      {number > 1 ? <Link href={`#step-${number - 1}`}>← Previous step</Link> : <span />}
      {number < count ? <Link href={`#step-${number + 1}`}>Continue to step {number + 1} →</Link> : <Link href="#open-questions">What remains open →</Link>}
    </div>
  </section>;
}

export default function ClassicalGodGuide() {
  const corpus = getCorpus();
  const report = getFrontierReport(GOD_ROOT_ID);
  const walkthrough = buildGodWalkthrough(corpus, report);
  const shortest = Math.min(...walkthrough.rootRoutes.map((route) => route.cost));
  const finalStep = walkthrough.stages.at(-1)!;
  const provedButUnestablished = new Set(walkthrough.route.proved_unestablished_statement_ids);
  const forestQuery = new URLSearchParams({ goal: GOD_ROOT_ID, compare: "STMT-BRUTE-ROOT-DISJUNCTION", sel: GOD_ROOT_ID });
  const graphQuery = new URLSearchParams({ view: "focus", node: GOD_ROOT_ID, sel: GOD_ROOT_ID });

  return <article className={styles.guide}>
    <header className={styles.intro}>
      <p className="eyebrow">Truth Core / Guided argument</p>
      <h1>From a necessary being to a classical-God conclusion</h1>
      <p>
        Follow three connected, formally checked results. See what each one really says, why the <em>same individual</em>
        survives the steps, and which philosophical commitments still need defending.
      </p>
      <div className={styles.realityCheck} role="note">
        <strong>Conditional conclusion, not an unconditional proof of God.</strong>
        Lean checks consequences given the encoded premises. It does not establish that those premises describe reality,
        that their source interpretations are correct, or that alternatives are false.
      </div>
      <dl className={styles.routeFacts}>
        <div><dt>Direct recorded routes to this conclusion</dt><dd>{walkthrough.rootRoutes.length}</dd></div>
        <div><dt>Fewest open leaves on any route</dt><dd>{shortest}</dd></div>
        <div><dt>Final assembly&apos;s named inputs</dt><dd>{finalStep.premises.length}</dd></div>
      </dl>
      <p className={styles.countNote}>
        The {finalStep.premises.length} names include an upstream result, not {finalStep.premises.length} independently justified primitives.
        The integration in <a href="https://github.com/moritzbrantner/truth-core/pull/917" target="_blank" rel="noreferrer">PR #917</a> discharged no philosophical premise.
      </p>
    </header>

    <nav className={styles.pathNav} aria-label="Walkthrough steps">
      <ol>{walkthrough.stages.map((stage, index) => <li key={stage.result.id}>
        <Link href={`#step-${index + 1}`}><span>{index + 1}</span>{stage.title}</Link>
      </li>)}</ol>
    </nav>

    <aside className={styles.prelude} aria-label="Necessary-being background">
      <div>
        <p className="eyebrow">Before the connected assembly</p>
        <h2>Why start with a necessary being?</h2>
        <p>
          An earlier result derives a concrete individual existing in the selected world and all accessible worlds,
          if its population, grounding and nontrapping premises hold. This is a <em>narrower related result</em>,
          not a claim that necessity alone entails perfection or a separate direct input to step 1.
        </p>
      </div>
      <Link href="/results/WHOLE-ROSTER-NECESSARY-CONCRETE">Inspect necessary-being result →</Link>
    </aside>

    {walkthrough.stages.map((stage, index) => <Stage key={stage.result.id} stage={stage}
      number={index + 1} count={walkthrough.stages.length} report={report} />)}

    <section className={styles.remaining} id="open-questions" aria-labelledby="remaining-title">
      <p className="eyebrow">The boundary of the result</p>
      <h2 id="remaining-title">What is not established yet?</h2>
      <p>
        The new assembly is one of {walkthrough.rootRoutes.length} recorded direct routes to this God-root statement.
        Its {walkthrough.route.premise_count} direct inputs expand to {walkthrough.route.cost} distinct open leaves through
        upstream dependencies. Changing the packaging did not remove any of those truth obligations.
      </p>
      <ul className={styles.boundaries}>
        <li><strong>Premises about reality.</strong> Grounding, modality, grades of being and causal transfer still need an applicable interpretation and warrant.</li>
        <li><strong>The attributes themselves.</strong> Infinite, eternal, intellect, will, goodness and the nine-attribute sufficiency interface retain explicit assumptions; this is not an independent proof of omniscience, moral perfection or free agency.</li>
        <li><strong>Personhood and rival worldviews.</strong> This theorem does not establish personhood, refute a coherent rival framework, or prove the historical and revelatory claims needed for Catholicism.</li>
      </ul>
      <details className={styles.technical}>
        <summary>Inspect all {walkthrough.openLeaves.length} open leaves of this route</summary>
        <div className={styles.technicalInner}>
          <p>
            This list is produced by the repository&apos;s frontier report for <Link href={`/statements/${GOD_ROOT_ID}`}>{GOD_ROOT_ID}</Link>.
            A leaf can have a conditional proof of its own while still lacking established supporting premises.
          </p>
          <ol className={styles.leafList}>{walkthrough.openLeaves.map((statement) => <li key={statement.id}>
            <div><Link href={`/statements/${statement.id}`}>{statement.paraphrase}</Link>
              {provedButUnestablished.has(statement.id) ? <span className={styles.inputRole}>Derived, but support still open</span> : null}
            </div>
            <Link href={`/dossiers/${statement.id}#dossier-instances`}>Sources, rivals and model checks</Link>
          </li>)}</ol>
        </div>
      </details>
      <div className={styles.finalLinks}>
        <Link href={`/forest?${forestQuery}`}>Explore this conclusion in the argument forest →</Link>
        <Link href={`/graph?${graphQuery}`}>Inspect the full proposition network →</Link>
        <Link href={`/results/${ASSEMBLY_RESULT_ID}`}>Read the final verified result →</Link>
      </div>
    </section>
  </article>;
}
