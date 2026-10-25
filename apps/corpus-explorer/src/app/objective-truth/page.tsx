import type { Metadata } from "next";
import Link from "next/link";

import { StatementStateMark } from "@/components/state-mark";
import { findStatement, getCorpus } from "@/lib/corpus";
import { getFrontierReport, statementState } from "@/lib/site-state";
import { getPilotScenarios, PILOT_GROUPS, pilotGraphHref } from "./pilot";

export const metadata: Metadata = { title: "Objective truth pilot — Truth Core" };

const scenarioLabels: Record<string, string> = {
  "unverified-cycle": "Arrows without verified results",
  "verified-reciprocal-only": "Verified A → B and B → A only",
  "grounded-reciprocal": "Both directions plus a premise-free proof of A",
};

export default function ObjectiveTruthPage() {
  const corpus = getCorpus();
  const report = getFrontierReport();
  const scenarios = getPilotScenarios();
  const bridgeIds = new Set(["STMT-PILOT-LOGICAL-SENTENCE-STABLE", "STMT-PILOT-NEGATION-RESPECTED"]);
  const obligations = report.items.filter((item) => bridgeIds.has(item.statement_id));
  const candidates = corpus.candidates.filter((item) => item.id === "OBJECTIVE-TRUTH-PROFILE-STABILITY-BRIDGE" || item.id === "RELATIVISM-GLOBAL-LOCAL-EPISTEMIC-WITNESSES");

  return (
    <>
      <h1 className="font-serif text-3xl">Objective truth, relativity, and the remaining bridges</h1>
      <p className="mt-3 max-w-3xl text-[var(--muted)]">
        Inspect the exact logical claims, their interpretations, and what remains unresolved.
        Establishment below is always within the displayed encoding and scope.
      </p>
      {PILOT_GROUPS.map((group) => (
        <section className="mt-9 border-t border-[var(--line)] pt-5" key={group.title}>
          <h2 className="font-serif text-2xl">{group.title}</h2>
          <p className="mt-2 max-w-3xl text-sm text-[var(--muted)]">{group.scope}</p>
          <ul className="mt-4 divide-y divide-[var(--line)]">
            {group.statementIds.map((id) => {
              const statement = findStatement(corpus, id);
              if (!statement) {
                throw new Error(`Missing pilot statement ${id}`);
              }
              const state = statementState(report, id);
              return (
                <li className="py-4" key={id}>
                  {state.kind === "unused" ? <span className="text-sm text-[var(--muted)]">Recorded reading · not established</span> : <StatementStateMark state={state} />}
                  <Link className="mt-2 block text-sm underline underline-offset-4" href={`/statements/${id}`}>{statement.paraphrase}</Link>
                  <div className="mt-2 flex flex-wrap gap-4 text-xs">
                    <code className="break-all text-[var(--muted)]">{id}</code>
                    <Link className="underline underline-offset-4" href={pilotGraphHref(id)}>Inspect graph and frontier</Link>
                  </div>
                </li>
              );
            })}
          </ul>
        </section>
      ))}
      <section className="mt-9 border-t border-[var(--line)] pt-5" aria-labelledby="reciprocal-heading">
        <h2 className="font-serif text-2xl" id="reciprocal-heading">Reciprocal entailment and grounding</h2>
        <p className="mt-2 max-w-3xl text-sm text-[var(--muted)]">
          A is ∃ P : Prop, P; B is ¬ (∀ P : Prop, ¬ P). The two verified implications preserve their distinct IDs.
          The comparison reuses the same statements and arrows with different available result records.
          A cycle of conditional results alone establishes neither proposition; a premise-free proof grounds the cluster.
        </p>
        <div className="mt-4 overflow-x-auto">
          <table className="w-full text-left text-sm">
            <caption className="sr-only">Authoritative frontier calculation for the reciprocal-entailment fixture</caption>
            <thead><tr><th className="py-2">Available evidence</th><th className="py-2">Verified results</th><th className="py-2">Established propositions</th></tr></thead>
            <tbody>{scenarios.map((scenario) => (
              <tr className="border-t border-[var(--line)]" key={scenario.id}>
                <td className="py-3 pr-4">{scenarioLabels[scenario.id] ?? scenario.id}</td>
                <td>{scenario.verifiedResults}</td>
                <td>{scenario.established.length ? "A and B" : "Neither"}</td>
              </tr>
            ))}</tbody>
          </table>
        </div>
        <p className="mt-3 flex flex-wrap gap-4 text-sm">
          <Link className="underline" href="/results/LOGIC-SOME-HOLDS-ENTAILS-NOT-ALL-FAIL">Proof of A → B</Link>
          <Link className="underline" href="/results/LOGIC-NOT-ALL-FAIL-ENTAILS-SOME-HOLDS">Proof of B → A</Link>
          <Link className="underline" href="/results/LOGIC-SOME-PROPOSITION-HOLDS">Independent proof of A</Link>
        </p>
      </section>
      <section className="mt-9 border-t border-[var(--line)] pt-5" aria-labelledby="pilot-frontier-heading">
        <h2 className="font-serif text-2xl" id="pilot-frontier-heading">Precise remaining frontier</h2>
        <ul className="mt-3 space-y-3">
          {obligations.map((item) => (
            <li key={item.statement_id}>
              <Link className="text-sm underline" href={pilotGraphHref(item.statement_id)}>{item.paraphrase}</Link>
              <p className="mt-1 text-xs text-[var(--muted)]">{item.depth === "bare" ? "No source claim yet states or supports this bridge." : "Sourced, but not yet defended."}</p>
            </li>
          ))}
          {candidates.map((item) => <li key={item.id}><Link className="text-sm underline" href={`/candidates/${item.id}`}>{item.goal}</Link></li>)}
        </ul>
        <p className="mt-4 text-sm text-[var(--muted)]">
          Refuting an explicit denial is different from refuting withheld assent.
          The pilot leaves <Link className="underline" href="/statements/STMT-EXCLUDED-MIDDLE-WITHHELD-INTUITIONISM">intuitionist withholding</Link> and the stronger interpretation bridges separate.
        </p>
      </section>
    </>
  );
}
