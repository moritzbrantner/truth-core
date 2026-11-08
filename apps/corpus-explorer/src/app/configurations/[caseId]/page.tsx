import Link from "next/link";
import { notFound } from "next/navigation";
import { Suspense } from "react";

import { getRegisteredConfigurationCases } from "@/lib/configuration-cases";
import { getCorpus, idOf, nameOf } from "@/lib/corpus";
import { getVerifiedConfigurations } from "@/lib/verified-configurations";

import { CertifiedWorkspace } from "./certified-workspace";

/** Display labels of every record id the configuration cites (ids stay opaque). */
function citedNames(value: unknown) {
  const ids = JSON.stringify(value).match(/[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}/g) ?? [];
  return Object.fromEntries([...new Set(ids)].map((id) => [id, nameOf(id)]));
}

export function generateStaticParams() {
  return (getVerifiedConfigurations()?.cases ?? getRegisteredConfigurationCases()).map((entry) => ({ caseId: entry.id }));
}

export default async function ConfigurationPage({ params }: { params: Promise<{ caseId: string }> }) {
  const { caseId } = await params;
  const bundle = getVerifiedConfigurations();
  const certified = bundle?.cases.find((entry) => entry.id === caseId);
  const configuration = bundle ? certified : getRegisteredConfigurationCases().find((entry) => entry.id === caseId);
  if (!configuration) {
    notFound();
  }
  const statements = getCorpus().statements;
  return <article className="max-w-5xl [overflow-wrap:anywhere]">
    <Link className="link-quiet text-sm" href={`/dossiers/${configuration.seed_statement_id}`}>← Seed dossier</Link>
    <h1 className="mt-6 font-serif text-3xl">Configuration assumptions</h1>
    <p className="mt-3 font-mono text-xs">{nameOf(configuration.id)} · {configuration.semantics.id}</p>
    {!certified ? <p className="mt-4 text-sm">Registered provenance · verification required</p> : null}
    {!certified ? <nav aria-label="Named assumption sets" className="mt-5 flex flex-wrap gap-4">
      {configuration.configurations.map((entry) => <a className="link-quiet text-sm" href={`#${entry.id}`} key={entry.id}>{nameOf(entry.id)}</a>)}
    </nav> : null}
    <details className="mt-6">
      <summary>Semantic settings</summary>
      <dl className="mt-3 grid gap-2 text-sm">{Object.entries(configuration.semantics).filter(([, value]) => typeof value === "string").map(([key, value]) => <div key={key}><dt className="font-medium">{key}</dt><dd>{value}</dd></div>)}</dl>
      <details className="mt-3 text-sm"><summary>Exact Lean bindings</summary><pre className="mt-3 whitespace-pre-wrap text-xs">{JSON.stringify(configuration.semantics, null, 2)}</pre></details>
    </details>
    {configuration.inapplicable_models.length > 0 ? <details className="mt-4 text-sm"><summary>Models excluded by this profile</summary>
      <ul className="mt-3 grid gap-2">{configuration.inapplicable_models.map((model) => <li key={model.model_id}>
        <span className="font-mono text-xs">{nameOf(model.model_id)}</span>
        {model.profile_mismatches.map((item) => <p key={item.parameter}>{item.parameter}: profile requires {item.expected}; registration uses {item.registered}</p>)}
      </li>)}</ul>
    </details> : null}
    {certified && bundle ? <Suspense fallback={<p className="mt-5 text-sm">Loading selected assumptions…</p>}>
      <CertifiedWorkspace configuration={certified} producer={bundle.producer} names={citedNames(certified)} statements={Object.fromEntries(statements.filter((statement) => certified.assumption_space.statement_ids.includes(statement.id)).map((statement) => [statement.id, { id: statement.id, paraphrase: statement.paraphrase }]))} />
    </Suspense> : configuration.configurations.map((entry) => <section className="record-section scroll-mt-6" id={entry.id} aria-labelledby={`${entry.id}-title`} key={entry.id}>
      <h2 className="font-serif text-2xl" id={`${entry.id}-title`}>{entry.id}</h2>
      <ul className="mt-3 grid gap-3">{entry.statement_ids.map((sid) => <li key={sid}>
        <Link className="link-quiet font-mono text-xs" href={`/statements/${sid}`}>{idOf(sid)}</Link>
        <p className="mt-1 text-sm">{statements.find((statement) => statement.id === sid)?.paraphrase}</p>
      </li>)}</ul>
      <p className="mt-4 text-sm">{entry.status}</p>
      {entry.incompatible_cores.map((core) => <div className="mt-4 text-sm" key={core.result_id}>
        <p>Registered incompatible core: {core.statement_ids.map(nameOf).join(", ")}</p>
        <Link className="link-quiet font-mono text-xs" href={`/results/${core.result_id}`}>{nameOf(core.result_id)}</Link>
        <p className="mt-1 font-mono text-xs">{core.theorem}</p>
        <p className="mt-1">{core.minimality}</p>
      </div>)}
      {entry.model_ids.length > 0 ? <p className="mt-3 text-sm">Registered matching models: {entry.model_ids.map(nameOf).join(", ")}</p> : null}
      <details className="mt-4 text-sm"><summary>Verify this assumption set</summary>
        <pre className="mt-3 whitespace-pre-wrap rounded border border-[var(--line)] p-3 text-xs">{`flock /tmp/moenarch/truth-core-heavy.lock python3 scripts/corpus.py configurations --case ${configuration.id}${entry.statement_ids.map((sid) => ` --premise ${sid}`).join("")} --json`}</pre>
      </details>
    </section>)}
    <p className="mt-6 text-sm text-[var(--muted)]">{configuration.scope}</p>
  </article>;
}
