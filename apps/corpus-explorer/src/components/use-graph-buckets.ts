"use client";

import { useEffect, useMemo, useState } from "react";

import {
  bucketPath,
  mergeBuckets,
  planBuckets,
  type GraphBucket,
  type GraphLookup,
  type GraphManifest,
  type GraphSearchIndex,
} from "@/lib/graph-bucket-view";
import type { GraphState } from "@/lib/graph-state";

const basePath = process.env.NEXT_PUBLIC_BASE_PATH ?? "";

/** Fetch each static JSON file once per page; failures are reported, not retried in a loop. */
const requests = new Map<string, Promise<unknown>>();
function fetchJson<T>(url: string): Promise<T> {
  let request = requests.get(url);
  if (!request) {
    request = fetch(url).then((response) => {
      if (!response.ok) throw new Error(`${response.status} ${url}`);
      return response.json();
    });
    request.catch(() => requests.delete(url));
    requests.set(url, request);
  }
  return request as Promise<T>;
}

/**
 * Loads the buckets the current view needs (#491) and merges them. Only the
 * buckets the plan names are shown, so deselecting a bucket removes it from the
 * map while its fetched file stays cached for this page.
 */
export function useGraphBuckets(manifest: GraphManifest, state: GraphState) {
  const [loaded, setLoaded] = useState<ReadonlyMap<string, GraphBucket>>(new Map());
  const [lookup, setLookup] = useState<GraphLookup | null>(null);
  const [search, setSearch] = useState<GraphSearchIndex | null>(null);
  const [error, setError] = useState("");
  const plan = useMemo(() => planBuckets(manifest, state, lookup, search), [manifest, state, lookup, search]);
  const url = (file: string) => bucketPath(basePath, file, manifest.version);

  useEffect(() => {
    if (!plan.needsLookup || lookup) return;
    let live = true;
    fetchJson<GraphLookup>(url("lookup")).then((data) => live && setLookup(data), (cause: Error) => live && setError(cause.message));
    return () => { live = false; };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [plan.needsLookup, lookup, manifest.version]);
  useEffect(() => {
    if (!plan.needsSearch || search) return;
    let live = true;
    fetchJson<GraphSearchIndex>(url("search")).then((data) => live && setSearch(data), (cause: Error) => live && setError(cause.message));
    return () => { live = false; };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [plan.needsSearch, search, manifest.version]);

  const wantedKey = plan.wanted.join("\n");
  useEffect(() => {
    let live = true;
    for (const id of wantedKey ? wantedKey.split("\n") : []) {
      if (loaded.has(id)) continue;
      fetchJson<GraphBucket>(url(id)).then(
        (bucket) => live && setLoaded((current) => (current.has(id) ? current : new Map([...current, [id, bucket]]))),
        (cause: Error) => live && setError(cause.message),
      );
    }
    return () => { live = false; };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [wantedKey, loaded, manifest.version]);

  const shown = plan.wanted.filter((id) => loaded.has(id));
  const shownKey = shown.join("\n");
  const merged = useMemo(
    () => mergeBuckets(manifest, shownKey ? shownKey.split("\n").map((id) => loaded.get(id) as GraphBucket) : []),
    // `loaded` only grows; the shown IDs decide the content.
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [manifest, shownKey],
  );
  const pending =
    shown.length < plan.wanted.length || (plan.needsLookup && !lookup) || (plan.needsSearch && !search);
  return { ...merged, wanted: plan.wanted, shown, pending: pending && !error, error };
}
