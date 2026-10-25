"use client";

import { useEffect, useRef, useState } from "react";
import { exploreProof, type ProofExploration, type ProofExplorationOptions } from "@/lib/proof-exploration";
import type { PropositionGraph } from "@/lib/proposition-graph";

export function useProofExploration(graph: PropositionGraph, enabled: boolean, options: Omit<ProofExplorationOptions, "signal">) {
  const [state, setState] = useState<{ running: boolean; result: ProofExploration | null }>({ running: false, result: null });
  const controller = useRef<AbortController | null>(null);
  const { target, budget, scope } = options;
  const scopeKey = scope ? JSON.stringify([...new Set(scope)].sort()) : "";
  useEffect(() => {
    const abort = new AbortController();
    controller.current = abort;
    let timer: ReturnType<typeof setTimeout>;
    const selectedScope: string[] | undefined = scopeKey ? JSON.parse(scopeKey) : undefined;
    const search = exploreProof(graph, { target, budget, scope: selectedScope, signal: abort.signal });
    const advance = () => {
      // Yield regularly so input and cancellation are observed even for a large
      // graph. The generator separately enforces the deterministic work budget.
      for (let count = 0; count < 40; count += 1) {
        const next = search.next();
        if (next.done) {
          setState({ running: false, result: next.value });
          return;
        }
      }
      timer = setTimeout(advance, 0);
    };
    timer = setTimeout(() => {
      if (!enabled || !target) {
        setState({ running: false, result: null });
        return;
      }
      setState({ running: true, result: null });
      timer = setTimeout(advance, 0);
    }, 0);
    return () => {
      abort.abort();
      clearTimeout(timer);
    };
  }, [graph, enabled, target, budget, scopeKey]);
  return { ...state, cancel: () => controller.current?.abort() };
}
