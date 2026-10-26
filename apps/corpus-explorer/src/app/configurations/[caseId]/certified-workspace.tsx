"use client";

import Link from "next/link";
import { useSearchParams } from "next/navigation";

import { selectedConfiguration } from "@/lib/configuration-selection";
import type { VerifiedConfigurationBundle, VerifiedConfigurationCase } from "@/lib/verified-configurations";

type Props = {
  configuration: VerifiedConfigurationCase;
  producer: VerifiedConfigurationBundle["producer"];
  statements: Record<string, { id: string; paraphrase: string }>;
};

export function CertifiedWorkspace({ configuration, producer, statements }: Props) {
  const query = useSearchParams();
  const preset = query.get("set");
  const defaultSet = configuration.configurations.find((entry) => entry.status === "model witnessed" && entry.statement_ids.includes(configuration.seed_statement_id)) ?? configuration.configurations[0];
  const namedSet = configuration.configurations.find((entry) => entry.id === preset);
  const custom = preset === "custom" || (preset === null && query.has("premise"));
  const chosen = custom ? query.getAll("premise") : (namedSet ?? defaultSet)?.statement_ids ?? [];
  const invalidPreset = preset !== null && preset !== "custom" && !namedSet;
  const selected = selectedConfiguration(configuration.assumption_space, chosen);
  const result = selected.terminal?.report;
  const implications = result?.status === "verified incompatible" ? [] : configuration.verified_implications.filter((entry) =>
    entry.premise_statement_ids.every((id) => chosen.includes(id)) && !chosen.includes(entry.conclusion_statement_id));
  function toggle(statementId: string) {
    const next = chosen.includes(statementId) ? chosen.filter((id) => id !== statementId) : [...chosen, statementId];
    const params = new URLSearchParams();
    params.set("set", "custom");
    for (const id of [...next].sort()) { params.append("premise", id); }
    window.history.replaceState(null, "", `${window.location.pathname}?${params.toString()}`);
  }
  return <>
    <nav aria-label="Named assumption sets" className="mt-5 flex flex-wrap gap-4">
      {configuration.configurations.map((entry) => <Link className="link-quiet text-sm" key={entry.id}
        href={`/configurations/${configuration.id}?set=${entry.id}`} scroll={false}>{entry.id}</Link>)}
    </nav>
    <fieldset className="mt-6 grid gap-4">
      <legend className="font-medium">Selected assumptions</legend>
      {configuration.assumption_space.statement_ids.map((id) => <label className="flex cursor-pointer items-start gap-3" key={id}>
        <input type="checkbox" className="mt-1 size-4 shrink-0" checked={chosen.includes(id)} onChange={() => toggle(id)} />
        <span><span className="block font-mono text-xs">{id}</span><span className="mt-1 block text-sm leading-6">{statements[id]?.paraphrase ?? id}</span></span>
      </label>)}
    </fieldset>
    {invalidPreset || selected.error ? <p role="alert" className="mt-5">{invalidPreset ? "This named assumption set is unavailable." : selected.error}</p> : null}
    {!invalidPreset && result ? <section className="record-section" aria-labelledby="configuration-status">
      <h2 id="configuration-status" className="font-serif text-2xl">{result.status}</h2>
      <p className="mt-2 text-sm">Verified during report generation · source {producer.source_head.slice(0, 12)}</p>
      {result.unresolved_reason ? <p className="mt-3 text-sm">{result.unresolved_reason}</p> : null}
      {result.incompatible_cores.map((core) => <div className="mt-5" key={core.result_id}>
        <h3 className="font-medium">Certified incompatible core</h3>
        <ul className="mt-2">{core.statement_ids.map((id) => <li key={id}><Link className="link-quiet font-mono text-xs" href={`/statements/${id}`}>{id}</Link></li>)}</ul>
        <p className="mt-2 text-sm">{core.minimality}</p>
        <ol className="mt-3 grid gap-2">{core.result_ids.map((id, index) => <li key={id}>
          <Link className="link-quiet font-mono text-xs" href={`/results/${id}`}>{id}</Link>
          <p className="mt-1 font-mono text-xs">{core.theorems[index]}</p>
        </li>)}</ol>
        <details className="mt-3 text-sm"><summary>Single-premise removal evidence</summary>
          <ul className="mt-2">{core.removal_evidence.map((entry) => <li key={entry.removed_statement_id}>{entry.removed_statement_id}: {entry.model_ids.join(", ") || "no matching certified witness"}</li>)}</ul>
        </details>
      </div>)}
      {result.model_witnesses.map((model) => <div className="mt-5" key={model.model_id}>
        <h3 className="font-mono text-xs">{model.model_id}</h3>
        <p className="mt-2 text-sm">This assignment satisfies every selected statement in the named formal profile.</p>
        <details className="mt-3 text-sm"><summary>Selected evaluations and certificates</summary>
          <p className="mt-2 font-mono text-xs">{model.lean_declaration}</p>
          <ul className="mt-2 grid gap-2">{model.evaluations.filter((entry) => chosen.includes(entry.statement_id)).map((entry) => <li key={entry.statement_id}>
            <p className="font-mono text-xs">{entry.statement_id}</p><p className="mt-1 font-mono text-xs">{entry.theorem}</p>
          </li>)}</ul>
        </details>
      </div>)}
      {implications.length > 0 ? <div className="mt-5"><h3 className="font-medium">Verified conditional applications</h3>
        <ul className="mt-2 grid gap-3">{implications.map((entry) => <li key={entry.result_id}>
          <Link className="link-quiet font-mono text-xs" href={`/statements/${entry.conclusion_statement_id}`}>{entry.conclusion_statement_id}</Link>
          <p className="mt-1 text-sm">From {entry.premise_statement_ids.join(", ")}</p>
          <Link className="link-quiet font-mono text-xs" href={`/results/${entry.result_id}`}>{entry.result_id}</Link>
          <p className="mt-1 font-mono text-xs">{entry.theorem}</p>
        </li>)}</ul>
      </div> : null}
      {result.core_composition.truncated ? <p className="mt-4 text-sm">The implication/core search reached its reported bound; completeness is unresolved.</p> : null}
    </section> : null}
    <details className="mt-5 text-sm"><summary>Verification provenance and limits</summary>
      <p className="mt-3">{producer.trust}</p>
      <p className="mt-2 font-mono text-xs">Input digest: {producer.input_digest}</p>
      <p className="mt-2">{configuration.assumption_space.limits.note}</p>
      <p className="mt-2">{configuration.assumption_space.statement_ids.length} assumption dimensions; bound {configuration.assumption_space.max_dimensions}. {configuration.assumption_space.limits.classifier_calls} canonical classifications produced {configuration.assumption_space.limits.terminal_families} pruned families covering {configuration.assumption_space.limits.covered_selections} syntactic selections.</p>
      <p className="mt-2">Selections do not discharge root premises. <Link className="link-quiet" href={`/dossiers/${configuration.seed_statement_id}`}>Inspect the authoritative route contribution.</Link></p>
    </details>
  </>;
}
