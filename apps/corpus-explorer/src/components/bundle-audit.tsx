import Link from "next/link";
import { auditRecordHref, type BundleAudit } from "@/lib/bundle-audit";

export function BundleAuditSection({ audit }: { audit?: BundleAudit }) {
  if (!audit) return null;
  const counts = new Map<string, number>();
  audit.records.forEach((row) => counts.set(row.kind, (counts.get(row.kind) ?? 0) + 1));
  return <section className="record-section min-w-0" id="bundle-audit" aria-label="Bounded bundle audit">
    <p className="eyebrow">Reviewed migration · bounded coverage</p>
    <h2 className="mt-3 font-serif text-2xl">{audit.title}</h2>
    <p className="mt-3 break-all text-xs text-[var(--muted)]">Before: {audit.base_head}</p>
    <p className="mt-3 text-sm leading-6">{audit.premise_delta}</p>
    <p className="mt-3 text-sm" data-audit-coverage>{audit.records.length} record dispositions: {[...counts].map(([kind, n]) => `${n} ${kind}`).join(" · ")}</p>
    <p className="mt-3 text-sm leading-6 text-[var(--muted)]">This is a reviewed scope inventory. The complete-expression contract checks the assembly result against its frozen Challenge, including its parameter context and project definition dependencies. Proof verification and semantic adequacy remain separate obligations.</p>
    <details className="mt-5" data-audit-records>
      <summary className="cursor-pointer font-serif text-xl">Exact records and remaining obligations</summary>
      <ul className="mt-4 grid gap-4">
        {audit.records.map((row) => {
          const href = auditRecordHref(row.kind, row.id);
          return <li className="min-w-0 border-l border-[var(--line)] pl-3 text-sm leading-6" key={`${row.kind}/${row.id}`}>
            <p className="break-all font-mono text-xs">{href ? <Link className="link-quiet" href={href}>{row.id}</Link> : row.id}</p>
            <p className="eyebrow mt-1">{row.status} · {row.classification.replaceAll("_", " ")}</p>
            <p>{row.finding}</p>
            <details className="mt-1 text-xs text-[var(--muted)]">
              <summary className="cursor-pointer">Exact record inputs</summary>
              <p className="break-all">{row.path}</p>
              <p className="break-all">Before SHA-256: {row.before.sha256}</p>
              <p className="break-all">Reviewed SHA-256: {row.reviewed_sha256}</p>
            </details>
          </li>;
        })}
      </ul>
    </details>
    <div className="mt-5" aria-label="Audit limits and unresolved bridges">
      <h3 className="eyebrow">Limits and unresolved bridges</h3>
      <ul className="mt-3 grid gap-3 text-sm leading-6">{audit.limits.map((limit) => <li key={limit}>{limit}</li>)}</ul>
    </div>
    <p className="mt-5 text-sm leading-6">Next scope: {audit.next_scope}</p>
  </section>;
}
