import Link from "next/link";
import { NextWorkMap } from "@/components/next-work-map";
import { DepthMark } from "@/components/state-mark";
import type { NextDerivation, NextLeaf, NextRival, NextStepsReport } from "@/lib/next-steps";
import { getFrontierReport } from "@/lib/site-state";
import { idOf, nameOf } from "@/lib/corpus";

export const metadata = { title: "What to work on next — Truth Core" };

function StatementLinks({ ids }: { ids: string[] }) {
  return ids.length ? <ul className="mt-1 space-y-1">{ids.map((id) => <li key={id}><Link className="link-quiet break-all text-xs" href={`/statements/${id}`}>{id}</Link></li>)}</ul> : <span>none</span>;
}
function Derivation({ proof }: { proof: NextDerivation }) {
  return <li className="my-2">
    <p className="break-all text-xs">{nameOf(proof.argument_id)} · {proof.verified ? "verified" : "no verified result"}{proof.transcription ? " · transcription" : ""}</p>
    <p className="mt-1 text-sm text-[var(--muted)]">{proof.meaning}</p>
    <p className="mt-1 text-sm">Premises still to establish:</p><StatementLinks ids={proof.missing_statement_ids} />
    {proof.result_ids.map((id) => <Link key={id} className="link-quiet mr-3 text-xs" href={`/results/${id}`}>Result {id}</Link>)}
  </li>;
}
function Rival({ rival }: { rival: NextRival }) {
  return <li className="my-3">
    <Link className="link-quiet text-sm" href={`/statements/${rival.statement_id}`}>{rival.paraphrase}</Link>
    <p className="text-xs">{rival.refuted ? "Refuted by a counted certificate" : "Undefeated"}</p>
    {!rival.refutations.length ? <p className="text-xs text-[var(--muted)]">No refutation recorded.</p> : <ul>{rival.refutations.map((refutation) => <li key={refutation.argument_id} className="mt-2 text-xs">
      {nameOf(refutation.argument_id)}: {refutation.counted ? "counts: all premises established" : refutation.verified ? "verified but does not count" : "not verified"}
      {!refutation.counted ? <><p>Unestablished premises:</p><StatementLinks ids={refutation.unestablished_premise_statement_ids} /></> : null}
    </li>)}</ul>}
    <details className="mt-2 text-sm"><summary>Recorded consequences under their complete premises ({rival.consequences.length})</summary><ul>{rival.consequences.map((proof) => <Derivation key={proof.argument_id} proof={proof} />)}</ul></details>
  </li>;
}
function Leaf({ leaf }: { leaf: NextLeaf }) {
  return <li id={`leaf-${leaf.statement_id}`} className="scroll-mt-5 rounded border border-[var(--line)] p-5">
    <div className="flex flex-wrap gap-2 text-xs">{leaf.depth ? <DepthMark depth={leaf.depth} /> : <span>Proved from open premises</span>}<span>{leaf.impact.routes_improved} routes improve · total cost drop {leaf.impact.total_cost_drop}</span></div>
    <h3 className="mt-2 font-serif text-xl"><Link className="link-quiet" href={`/statements/${leaf.statement_id}`}>{leaf.paraphrase}</Link></h3>
    <p className="mt-1 break-all font-mono text-xs text-[var(--muted)]">{idOf(leaf.statement_id)}</p>
    <p className="mt-3 text-sm"><strong>Owner decision:</strong> accepting this as floor requires approval. This is one possible settlement path, not a recommendation to accept it.</p>
    {leaf.definition_ids.length ? <p className="mt-2 text-sm">Definitions to inspect: {leaf.definition_ids.map((id) => <Link key={id} className="link-quiet mr-2" href={`/definitions/${id}`}>{id}</Link>)}. Adopting a different definition requires an explicit owner decision and a check of every use.</p> : null}
    {leaf.definition_decisions.map((action, i) => <p key={i} className="mt-2 text-sm">{action.kind} · {action.status}: {action.description} {action.decision ? <a className="link-quiet" href={action.decision}>{action.status === "approved" ? "Owner decision" : "Owner discussion"}</a> : null}</p>)}
    <details className="mt-3" open={leaf.derivations.length > 0}><summary>Derive: {leaf.derivations.length ? `${leaf.derivations.length} recorded arguments` : "no derivation recorded; find and verify one"}</summary><ul>{leaf.derivations.map((proof) => <Derivation key={proof.argument_id} proof={proof} />)}</ul></details>
    <details className="mt-3"><summary>Defend: {leaf.defense.undefeated_statement_ids.length} of {leaf.defense.recorded_rival_count} recorded rivals undefeated</summary>
      <p className="mt-2 text-sm text-[var(--muted)]">{leaf.defense.coverage}. An empty rival list does not establish a premise.</p>
      <ul>{leaf.rivals.map((rival) => <Rival key={rival.statement_id} rival={rival} />)}</ul>
    </details>
    <details className="mt-3 text-sm"><summary>Cost change for each affected route</summary><ul>{leaf.impact.routes.map((impact) => <li key={impact.argument_id} className="my-2 break-all text-xs">{impact.argument_id}: {impact.before} → {impact.after} ({impact.drop > 0 ? "−" : "+"}{Math.abs(impact.drop)})</li>)}</ul></details>
    <Link className="link-quiet mt-3 inline-block text-sm" href={`/dossiers/${leaf.statement_id}`}>Full premise dossier</Link>
  </li>;
}
function JointSettlements({ report }: { report: NextStepsReport }) {
  const summary = report.joint_settlement_summary;
  return <section id="joint-settlements" className="my-10">
    <h2 className="font-serif text-2xl">Joint settlement across routes</h2>
    <p className="my-3 text-sm text-[var(--muted)]">A route is a conjunction. Its failure means at least one leaf fails. To combine routes by incompatible failures, every failure mode on each side needs a consequence theorem, and the incompatibility needs settled premises. A recorded rival is not automatically the negation of its leaf. Overlap ranks opportunities; it proves no joint settlement.</p>
    {summary.pair_count ? <div className="my-4 rounded border border-[var(--line)] p-4">
      <h3 className="font-serif text-xl">Shared obligations across reported routes</h3>
      <p className="mt-2 text-sm">Among {summary.verified_route_count} reported verified routes ({summary.pair_count} pairs), the smallest pairwise overlap is {summary.minimum_pair_overlap} open premises. {summary.shared_by_all_reported_routes.length} open premises appear in every reported route. Combining these fixed route bundles cannot bypass those shared premises.</p>
      <p className="mt-2 text-xs text-[var(--muted)]">{summary.scope}</p>
      <details className="mt-3"><summary className="text-sm">Inspect all {summary.shared_by_all_reported_routes.length} shared obligations</summary>
        <ul className="mt-2 space-y-1">{summary.shared_by_all_reported_routes.map((sid) => <li key={sid}><Link className="link-quiet break-all text-xs" href={`#leaf-${sid}`}>{nameOf(sid)}</Link></li>)}</ul>
      </details>
    </div> : null}
    {report.joint_settlement_schema_result_ids.length ? <p className="my-3 text-sm">Reusable logical schemas (no concrete route pair certified): {report.joint_settlement_schema_result_ids.map((id) => <Link className="link-quiet mr-2" key={id} href={`/results/${id}`}>{id}</Link>)}</p> : null}
    <ul className="space-y-3">{report.joint_settlements.map((pair) => <li key={`${pair.left_argument_id}:${pair.right_argument_id}`} className="rounded border border-[var(--line)] p-4"><details>
      <summary className="break-all text-sm">{nameOf(pair.left_argument_id)} + {nameOf(pair.right_argument_id)} · {pair.overlap_count} shared open leaves · {pair.certified ? "certified" : "unresolved"}</summary>
      <p className="mt-3 text-sm">Shared failure modes:</p><StatementLinks ids={pair.shared_statement_ids} />
      <div className="mt-3 grid gap-4 sm:grid-cols-2">{[pair.left_failure_statement_ids, pair.right_failure_statement_ids].map((ids, side) => <div key={side}><h3 className="text-sm font-semibold">{side ? "Right" : "Left"} route: each possible failure</h3><ul>{ids.map((sid) => {
        return <li key={sid} className="my-2"><Link className="link-quiet break-all text-xs" href={`#failure-${sid}`}>¬ {sid}</Link></li>;
      })}</ul></div>)}</div>
      <p className="mt-3 text-sm">Remaining obligations:</p><ul className="list-disc pl-5 text-sm">{pair.remaining.map((text) => <li key={text}>{text}</li>)}</ul>
    </details></li>)}</ul>
    <h3 className="mt-6 font-serif text-xl">Failure modes and recorded consequences</h3>
    <p className="mt-2 text-sm text-[var(--muted)]">This index is shared by every pair above. The consequences belong to the recorded rival with all its premises; a bridge from the logical failure of the leaf is still required.</p>
    <ul className="mt-3 space-y-3">{Object.values(report.failure_modes).map((failure) => <li id={`failure-${failure.statement_id}`} key={failure.statement_id} className="scroll-mt-5 rounded border border-[var(--line)] p-3"><details><summary className="break-all text-xs">¬ {failure.statement_id}</summary><p className="my-2 text-sm">{failure.negation_consequence_coverage}</p><Link className="link-quiet text-sm" href={`#leaf-${failure.statement_id}`}>Open leaf and settlement actions</Link><ul>{failure.recorded_rivals.map((rival) => <Rival key={rival.statement_id} rival={rival} />)}</ul></details></li>)}</ul>
  </section>;
}

export default function NextPage() {
  const frontier = getFrontierReport();
  const report = frontier.next_steps;
  if (!report) throw new Error("The frontier report does not contain its next-work projection");
  const progress = report.progress;
  const supportedPremises = frontier.support_options.items.filter((item) => item.verified_alternative_bundles.length);
  return <article className="min-w-0 [overflow-wrap:anywhere]">
    <header><p className="eyebrow">Truth Core / Research direction</p><h1 className="mt-2 font-serif text-4xl">What to work on next</h1>
      <p className="mt-3 max-w-3xl text-sm text-[var(--muted)]">Start at <Link className="link-quiet" href={`/statements/${report.root?.statement_id}`}>{report.root?.paraphrase ?? "the root"}</Link>. Compare premise settlements and alternative support arguments first; expanded route cost is a diagnostic, not the progress KPI. Every status and count comes from the same frontier report as the CLI.</p>
    </header>
    <section className="my-8" aria-labelledby="support-heading">
      <h2 id="support-heading" className="font-serif text-2xl">Foundational progress and support options</h2>
      <ul className="mt-3 list-disc pl-5 text-sm">
        <li>{progress.root_reaching_established_count} root-reaching statements established in the corpus</li>
        <li>{progress.with_verified_alternative_count} of {progress.unestablished_premise_count} unestablished premises have a verified support alternative</li>
        <li>{progress.verified_alternative_bundle_count} distinct verified premise bundles, including established conclusions</li>
      </ul>
      <p className="mt-3 text-sm text-[var(--muted)]">A premise can be assumed directly or supported by a verified argument from other premises. Adding the latter is useful even when expanded leaf cost rises. Verification establishes the inference, not its open premises; bundle counts neither measure argument independence nor establish the root.</p>
      <details className="mt-3 rounded border border-[var(--line)] p-4"><summary className="text-sm">Inspect {supportedPremises.length} premises with verified alternatives</summary>
        <ul className="mt-4 space-y-4">{supportedPremises.map((item) => <li key={item.statement_id} className="border-t border-[var(--line)] pt-3">
          <Link className="link-quiet break-all text-sm" href={`/statements/${item.statement_id}`}>{item.statement_id}</Link>
          <p className="mt-1 text-xs text-[var(--muted)]">{item.established ? "Established in the corpus" : "Direct assumption remains available"}; {item.verified_alternative_bundles.length} distinct verified bundle(s):</p>
          <ul className="mt-2 space-y-2">{item.verified_alternative_bundles.map((bundle) => <li key={bundle.premise_statement_ids.join("|")} className="text-xs">
            <span>Premises:</span> {bundle.premise_statement_ids.length ? bundle.premise_statement_ids.map((id) => <Link key={id} className="link-quiet mr-2 break-all" href={`/statements/${id}`}>{id}</Link>) : "none"}
            <p className="mt-1">Arguments: {bundle.argument_ids.join(", ")}</p>
            <p className="mt-1">Verified results: {bundle.result_ids.map((id) => <Link key={id} className="link-quiet mr-2 break-all" href={`/results/${id}`}>{id}</Link>)}</p>
          </li>)}</ul>
        </li>)}</ul>
      </details>
    </section>
    <section className="my-6 grid gap-4 sm:grid-cols-3" aria-label="Three ways to settle a premise">{Object.entries(report.settlement_rules).map(([kind, text]) => <div key={kind} className="rounded border border-[var(--line)] p-4"><h2 className="font-serif text-xl capitalize">{kind}</h2><p className="mt-2 text-sm">{text}</p></div>)}</section>
    <section aria-labelledby="owner-decisions-heading" className="my-8"><h2 id="owner-decisions-heading" className="font-serif text-2xl">Recorded owner decisions</h2><p className="mt-2 text-sm text-[var(--muted)]">Specific decision requests or approvals already linked from leaf records, ranked by settlement impact. These differ from the general option of proposing any premise as a new floor item.</p>{!report.owner_decisions.length ? <p className="mt-3 text-sm">No specific floor or definition decision request is recorded on the current open route leaves.</p> : null}<ul className="mt-3 space-y-3">{report.owner_decisions.map((entry) => <li key={entry.statement_id} className="rounded border border-[var(--line)] p-4"><Link className="link-quiet" href={`#leaf-${entry.statement_id}`}>{entry.paraphrase}</Link><p className="mt-1 text-xs">{entry.impact.routes_improved} routes improve if settled · total cost drop {entry.impact.total_cost_drop}</p>{entry.actions.map((action, i) => <p key={i} className="mt-2 text-sm">{action.kind} · {action.status}: {action.description} {action.decision ? <a className="link-quiet" href={action.decision}>{action.status === "approved" ? "Owner decision" : "Owner discussion"}</a> : null}</p>)}</li>)}</ul></section>
    <NextWorkMap dag={report.dag} routes={report.routes} root={report.root}
      names={Object.fromEntries(report.dag.arguments.map((argument) => [argument.argument_id, nameOf(argument.argument_id)]))} />
    <section aria-labelledby="routes-heading"><h2 id="routes-heading" className="font-serif text-2xl">Expanded-route cost (diagnostic)</h2>
      <p className="mt-2 text-sm text-[var(--muted)]">A new conditional argument may increase this expanded leaf count without reducing the available ways to support its conclusion. Rankings here prioritize compact expansions only.</p>
      <div className="mt-3 overflow-x-auto"><table className="w-full text-left text-sm"><thead><tr><th className="p-2">Rank</th><th className="p-2">Route</th><th className="p-2">Cost</th><th className="p-2">Joint settlement</th></tr></thead><tbody>{report.routes.map((route, rank) => <tr key={route.argument_id} className="border-t border-[var(--line)]"><td className="p-2">{rank + 1}</td><td className="p-2"><p className="break-all">{route.argument_id}</p><p className="text-xs text-[var(--muted)]">{route.cheapest ? "Cheapest · " : ""}{route.verified ? "verified" : "unverified"}{route.designated ? " · designated route" : ""}{route.transcription ? " · transcription" : ""}</p></td><td className="p-2">{route.cost}</td><td className="p-2"><Link className="link-quiet" href="#joint-settlements">Unresolved: inspect all failure modes</Link></td></tr>)}</tbody></table></div>
    </section>
    <section className="my-10" aria-labelledby="leaves-heading"><h2 id="leaves-heading" className="font-serif text-2xl">Open leaves in the lowest-cost expansion</h2><p className="mt-3 text-sm text-[var(--muted)]">Diagnostic priority by route-cost improvement, not the full research-value ranking. Source depth and settlement are different: stated and supported premises remain open.</p><p className="mt-2 text-xs text-[var(--muted)]">{report.impact_scope}</p><ul className="mt-5 space-y-4">{report.leaves.filter((leaf) => leaf.on_cheapest_route).map((leaf) => <Leaf key={leaf.statement_id} leaf={leaf} />)}</ul>
      <details className="mt-5"><summary>Open leaves unique to other routes</summary><ul className="mt-4 space-y-4">{report.leaves.filter((leaf) => !leaf.on_cheapest_route).map((leaf) => <Leaf key={leaf.statement_id} leaf={leaf} />)}</ul></details>
    </section>
    <section className="my-10" aria-labelledby="partitions-heading"><h2 id="partitions-heading" className="font-serif text-2xl">Disjunction and partition opportunities</h2><p className="my-3 text-sm text-[var(--muted)]">An excluded-middle case split can establish a target after the other covered cases are defeated and every background premise is settled. A list of worldviews alone is not exhaustive.</p><ul>{report.partitions.map((partition) => <li key={partition.result_id} className="my-4 rounded border border-[var(--line)] p-5"><Link className="link-quiet" href={`/results/${partition.result_id}`}>{nameOf(partition.result_id)}</Link><p className="mt-2 text-sm">Target: <Link className="link-quiet" href={`/statements/${partition.target_statement_id}`}>{nameOf(partition.target_statement_id)}</Link> · {partition.target_established ? "established" : "open"}</p><p className="mt-2 text-sm">Coverage background still to establish:</p><StatementLinks ids={partition.missing_background_statement_ids} /><ul className="mt-3 list-disc pl-5">{partition.cases.map((cell) => <li key={cell.lean_declaration} className="my-2 text-sm">{cell.label}: {cell.refuted ? "refuted" : "undefeated"}<p className="break-all font-mono text-xs">{cell.lean_declaration}</p><p className="text-xs text-[var(--muted)]">{cell.refutation_scope}</p></li>)}</ul><p className="mt-2 text-sm text-[var(--muted)]">{partition.note}</p>{partition.survival_result_id ? <Link className="link-quiet text-sm" href={`/results/${partition.survival_result_id}`}>Inspect surviving-case witnesses</Link> : null}</li>)}</ul></section>
    <JointSettlements report={report} />
    <section id="floor-register" className="my-10"><h2 className="font-serif text-2xl">Explicit floor register</h2><p className="my-3 text-sm text-[var(--muted)]">This register displays the corpus’s existing floor markings and owner approvals. It adds no floor item.</p><ul className="space-y-3">{report.floor_register.map((entry) => <li key={entry.statement_id} className="rounded border border-[var(--line)] p-4"><Link className="link-quiet" href={`/statements/${entry.statement_id}`}>{entry.paraphrase}</Link><p className="mt-1 text-xs">{entry.basis} · {entry.met ? "basis met" : "basis not met"} · {entry.dependents.arguments.length} dependent arguments{entry.reaches_root ? " · reaches root" : ""}</p>{entry.owner_approval ? <a className="link-quiet text-sm" href={entry.owner_approval.decision}>Owner approval</a> : <p className="text-xs">No owner approval recorded.</p>}{entry.reasons.length ? <p className="text-sm">{entry.reasons.join("; ")}</p> : null}<details className="mt-2 text-sm"><summary>Recorded rivals ({entry.rivals.length}) and dependencies</summary><ul>{entry.rivals.map((rival) => <Rival key={rival.statement_id} rival={rival} />)}</ul><StatementLinks ids={entry.dependents.statements} /></details></li>)}</ul></section>
  </article>;
}
