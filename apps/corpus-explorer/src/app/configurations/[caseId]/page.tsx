import Link from "next/link";
import { notFound } from "next/navigation";

import { getRegisteredConfigurationCases } from "@/lib/configuration-cases";
import { getCorpus } from "@/lib/corpus";

export function generateStaticParams() {
  return getRegisteredConfigurationCases().map((entry) => ({ caseId: entry.id }));
}

export default async function ConfigurationPage({ params }: { params: Promise<{ caseId: string }> }) {
  const { caseId } = await params;
  const configuration = getRegisteredConfigurationCases().find((entry) => entry.id === caseId);
  if (!configuration) {
    notFound();
  }
  const statements = getCorpus().statements;
  return <article className="max-w-5xl [overflow-wrap:anywhere]">
    <Link className="link-quiet text-sm" href={`/dossiers/${configuration.seed_statement_id}`}>← Seed dossier</Link>
    <h1 className="mt-6 font-serif text-3xl">Configuration assumptions</h1>
    <p className="mt-3 font-mono text-xs">{configuration.id} · {configuration.semantics.id}</p>
    <p className="mt-4 text-sm">Registered provenance · verification required</p>
    <nav aria-label="Named assumption sets" className="mt-5 flex flex-wrap gap-4">
      {configuration.configurations.map((entry) => <a className="link-quiet text-sm" href={`#${entry.id}`} key={entry.id}>{entry.id}</a>)}
    </nav>
    <details className="mt-6">
      <summary>Semantic settings</summary>
      <dl className="mt-3 grid gap-2 text-sm">{Object.entries(configuration.semantics).filter(([, value]) => typeof value === "string").map(([key, value]) => <div key={key}><dt className="font-medium">{key}</dt><dd>{value}</dd></div>)}</dl>
      <details className="mt-3 text-sm"><summary>Exact Lean bindings</summary><pre className="mt-3 whitespace-pre-wrap text-xs">{JSON.stringify(configuration.semantics, null, 2)}</pre></details>
    </details>
    {configuration.inapplicable_models.length > 0 ? <details className="mt-4 text-sm"><summary>Models excluded by this profile</summary>
      <ul className="mt-3 grid gap-2">{configuration.inapplicable_models.map((model) => <li key={model.model_id}>
        <span className="font-mono text-xs">{model.model_id}</span>
        {model.profile_mismatches.map((item) => <p key={item.parameter}>{item.parameter}: profile requires {item.expected}; registration uses {item.registered}</p>)}
      </li>)}</ul>
    </details> : null}
    {configuration.configurations.map((entry) => <section className="record-section scroll-mt-6" id={entry.id} aria-labelledby={`${entry.id}-title`} key={entry.id}>
      <h2 className="font-serif text-2xl" id={`${entry.id}-title`}>{entry.id}</h2>
      <ul className="mt-3 grid gap-3">{entry.statement_ids.map((sid) => <li key={sid}>
        <Link className="link-quiet font-mono text-xs" href={`/statements/${sid}`}>{sid}</Link>
        <p className="mt-1 text-sm">{statements.find((statement) => statement.id === sid)?.paraphrase}</p>
      </li>)}</ul>
      <p className="mt-4 text-sm">{entry.status}</p>
      {entry.incompatible_cores.map((core) => <div className="mt-4 text-sm" key={core.result_id}>
        <p>Registered incompatible core: {core.statement_ids.join(", ")}</p>
        <Link className="link-quiet font-mono text-xs" href={`/results/${core.result_id}`}>{core.result_id}</Link>
        <p className="mt-1 font-mono text-xs">{core.theorem}</p>
        <p className="mt-1">{core.minimality}</p>
      </div>)}
      {entry.model_ids.length > 0 ? <p className="mt-3 text-sm">Registered matching models: {entry.model_ids.join(", ")}</p> : null}
      <details className="mt-4 text-sm"><summary>Verify this assumption set</summary>
        <pre className="mt-3 whitespace-pre-wrap rounded border border-[var(--line)] p-3 text-xs">{`flock /tmp/moenarch/truth-core-heavy.lock python3 scripts/corpus.py configurations --case ${configuration.id}${entry.statement_ids.map((sid) => ` --premise ${sid}`).join("")} --json`}</pre>
      </details>
    </section>)}
    <p className="mt-6 text-sm text-[var(--muted)]">{configuration.scope}</p>
  </article>;
}
