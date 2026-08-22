"use client";

import Link from "next/link";
import { usePathname, useRouter, useSearchParams } from "next/navigation";
import { useMemo } from "react";

import { StatusMark } from "@/components/status-mark";
import type { ClaimListEntry, CorpusSource } from "@/lib/corpus";

type ClaimExplorerProps = {
  claims: ClaimListEntry[];
  sources: CorpusSource[];
};

function sourceLabel(claim: ClaimListEntry) {
  return `${claim.author}, ${claim.work}`;
}

export function ClaimExplorer({ claims, sources }: ClaimExplorerProps) {
  const pathname = usePathname();
  const router = useRouter();
  const searchParams = useSearchParams();
  const query = searchParams.get("q") ?? "";
  const source = searchParams.get("source") ?? "";
  const status = searchParams.get("status") ?? "";

  const visibleClaims = useMemo(() => {
    const normalizedQuery = query.trim().toLowerCase();

    return claims.filter((claim) => {
      const matchesQuery =
        !normalizedQuery ||
        [claim.paraphrase, claim.author, claim.work, claim.locator, claim.id]
          .join(" ")
          .toLowerCase()
          .includes(normalizedQuery);
      const matchesSource = !source || claim.sourceId === source;
      const matchesStatus = !status || claim.status === status;

      return matchesQuery && matchesSource && matchesStatus;
    });
  }, [claims, query, source, status]);

  function updateParameter(name: string, value: string) {
    const params = new URLSearchParams(searchParams.toString());
    if (value) {
      params.set(name, value);
    } else {
      params.delete(name);
    }

    const queryString = params.toString();
    router.replace(queryString ? `${pathname}?${queryString}` : pathname, { scroll: false });
  }

  return (
    <section aria-labelledby="claim-index-heading" className="mt-12">
      <div className="flex flex-col justify-between gap-5 border-y border-[var(--line)] py-5 lg:flex-row lg:items-end">
        <div>
          <p className="eyebrow">Corpus index</p>
          <h2 className="mt-2 font-serif text-3xl tracking-[-0.035em]" id="claim-index-heading">
            Source-derived claims
          </h2>
        </div>
        <p aria-live="polite" className="text-sm text-[var(--muted)]">
          {visibleClaims.length} of {claims.length} claims
        </p>
      </div>

      <div className="grid gap-3 border-b border-[var(--line)] py-5 md:grid-cols-[minmax(0,1fr)_12rem_10rem]">
        <label className="field-label">
          Search claims
          <input
            className="field-control"
            onChange={(event) => updateParameter("q", event.target.value)}
            placeholder="Search source, locator, or reading"
            type="search"
            value={query}
          />
        </label>
        <label className="field-label">
          Source
          <select className="field-control" onChange={(event) => updateParameter("source", event.target.value)} value={source}>
            <option value="">All sources</option>
            {sources.map((item) => (
              <option key={item.id} value={item.id}>
                {item.author}, {item.work}
              </option>
            ))}
          </select>
        </label>
        <label className="field-label">
          Status
          <select className="field-control" onChange={(event) => updateParameter("status", event.target.value)} value={status}>
            <option value="">All statuses</option>
            <option value="formalized">Formalized</option>
          </select>
        </label>
      </div>

      <div className="divide-y divide-[var(--line)]">
        {visibleClaims.map((claim) => (
          <article className="grid gap-4 py-6 md:grid-cols-[12rem_minmax(0,1fr)_auto] md:gap-8" key={claim.id}>
            <div className="text-sm leading-6 text-[var(--muted)]">
              <Link className="link-quiet" href={`/sources/${claim.sourceId}`}>
                {sourceLabel(claim)}
              </Link>
              <p>{claim.locator}</p>
            </div>
            <div>
              <Link className="group" href={`/claims/${claim.id}`}>
                <h3 className="font-serif text-2xl leading-tight tracking-[-0.025em] group-hover:text-[var(--accent)]">
                  {claim.paraphrase}
                </h3>
              </Link>
              <p className="mt-2 text-sm text-[var(--muted)]">{claim.id}</p>
            </div>
            <div className="flex items-start gap-2 md:flex-col md:items-end">
              <StatusMark>Formalized</StatusMark>
              {claim.hasVerifiedArgument ? <StatusMark tone="accent">Verified argument</StatusMark> : null}
            </div>
          </article>
        ))}
        {!visibleClaims.length ? (
          <p className="py-10 text-[var(--muted)]">No claims match these filters.</p>
        ) : null}
      </div>
    </section>
  );
}
