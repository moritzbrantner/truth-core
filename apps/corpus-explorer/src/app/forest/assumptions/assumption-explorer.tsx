"use client";

import Link from "next/link";
import { useRouter, useSearchParams } from "next/navigation";
import { useEffect, useMemo, useRef, useState } from "react";

import type { ForestTreeModel } from "@/lib/argument-forest";
import { buildAssumptionRelevance, rankImplications, rankPropositionMatches } from "@/lib/assumption-relevance";
import { exploreAssumptions } from "@/lib/argument-scenarios";
import { activeCertifiedCores, reviewNewBelief, type CertifiedBeliefCore } from "@/lib/belief-conflicts";
import { BELIEF_STORAGE_KEY, chooseBelief, EMPTY_BELIEFS, readBeliefProfile, rejectBeliefs, writeBeliefProfile, type BeliefProfile } from "@/lib/belief-profile";
import { toggleOpenPath } from "@/lib/tree-open-paths";
import { StatementBranch } from "../forest-explorer";
import styles from "../forest.module.css";
import { ConflictReview } from "./conflict-review";
import { shortId } from "@/lib/corpus-ids";

function profileFromQuery(values: URLSearchParams, known: ReadonlySet<string>): BeliefProfile {
  return readBeliefProfile(JSON.stringify({ version: 1, accepted: values.getAll("yes"), denied: values.getAll("no") }), known);
}

export function AssumptionExplorer({ model, certifiedCores, hasCertifiedEvidence }: {
  model: ForestTreeModel;
  certifiedCores: CertifiedBeliefCore[];
  hasCertifiedEvidence: boolean;
}) {
  const router = useRouter();
  const params = useSearchParams();
  const [search, setSearch] = useState("");
  const [resultFilter, setResultFilter] = useState("");
  const [saved, setSaved] = useState<BeliefProfile | null>(null);
  const [storageAvailable, setStorageAvailable] = useState(true);
  const [pending, setPending] = useState<string | null>(null);
  const [pendingReversal, setPendingReversal] = useState<{ id: string; value: "true" | "false" } | null>(null);
  const [confirmClear, setConfirmClear] = useState(false);
  const [confirmReplace, setConfirmReplace] = useState(false);
  const [shareLink, setShareLink] = useState<string | null>(null);
  const known = useMemo(() => new Set(Object.keys(model.statements)), [model]);
  // Compose updates issued before the previous router.replace commits, so rapid
  // interactions build on each other instead of on the last rendered URL.
  const pendingQuery = useRef<string | null>(null);
  useEffect(() => {
    pendingQuery.current = null;
  }, [params]);
  useEffect(() => {
    function refresh() {
      // Another tab changed the saved beliefs; an unanswered proposal no longer applies.
      setPending(null);
      setPendingReversal(null);
      try {
        setSaved(readBeliefProfile(window.localStorage.getItem(BELIEF_STORAGE_KEY), known));
      } catch {
        setStorageAvailable(false);
        setSaved(EMPTY_BELIEFS);
      }
    }
    refresh();
    const onStorage = (event: StorageEvent) => {
      if (event.key === BELIEF_STORAGE_KEY || event.key === null) { refresh(); }
    };
    window.addEventListener("storage", onStorage);
    return () => window.removeEventListener("storage", onStorage);
  }, [known]);

  const goal = model.statements[params.get("goal") ?? ""] ? params.get("goal")! : model.defaultGoal;
  // A shared URL is an explicit, unsaved preview; never import it on page load.
  const preview = params.has("preview") || params.has("yes") || params.has("no");
  // Keyed on the belief entries only, so tree toggles and goal changes do not rerun the scenario.
  const previewKey = JSON.stringify([params.getAll("yes"), params.getAll("no")]);
  const fromUrl = useMemo(() => {
    const [accepted, denied] = JSON.parse(previewKey) as [string[], string[]];
    return readBeliefProfile(JSON.stringify({ version: 1, accepted, denied }), known);
  }, [known, previewKey]);
  const active = preview ? fromUrl : saved ?? EMPTY_BELIEFS;
  const scenario = useMemo(() => exploreAssumptions(model, active.accepted, active.denied), [model, active]);
  const relevance = useMemo(() => buildAssumptionRelevance(model, goal, scenario), [model, goal, scenario]);
  const activeCores = activeCertifiedCores(scenario.accepted, certifiedCores);
  const pendingReview = pending ? reviewNewBelief(new Set(saved?.accepted ?? []), pending, certifiedCores) : null;
  const expanded = new Set(params.has("open") ? params.getAll("open") : ["root"]);
  const query = search.trim().toLowerCase();
  const choices = useMemo(() => query.length >= 2 ? rankPropositionMatches(model, query, relevance, scenario) : [],
    [model, query, relevance, scenario]);
  const matches = useMemo(() => rankImplications(scenario.derived, relevance).filter(([id]) => {
    const value = resultFilter.trim().toLowerCase();
    return !value || id.toLowerCase().includes(value) || model.statements[id]?.paraphrase.toLowerCase().includes(value);
  }), [model, relevance, resultFilter, scenario]);
  const selectedIds = [...scenario.accepted, ...scenario.denied].sort((a, b) =>
    (relevance.goalDistance.get(a) ?? Infinity) - (relevance.goalDistance.get(b) ?? Infinity) || a.localeCompare(b));

  function update(change: (next: URLSearchParams) => void) {
    const next = new URLSearchParams(pendingQuery.current ?? params.toString());
    change(next);
    const query = next.toString();
    pendingQuery.current = query;
    // Not `next.size`: that getter is missing in Safari 16.x and Chrome/Firefox 111-112.
    router.replace("/forest/assumptions" + (query ? "?" + query : ""), { scroll: false });
  }

  function persist(profile: BeliefProfile) {
    setSaved(profile);
    setShareLink(null);
    // Any saved change supersedes an unanswered conflict or reversal review.
    setPending(null);
    setPendingReversal(null);
    try {
      window.localStorage.setItem(BELIEF_STORAGE_KEY, writeBeliefProfile(profile));
    } catch {
      // In restricted browsers, selections still work for this tab but will not survive a reload.
      setStorageAvailable(false);
    }
  }

  function clearPreview() {
    setConfirmReplace(false);
    setShareLink(null);
    update((next) => { next.delete("yes"); next.delete("no"); next.delete("preview"); });
  }

  function copyScenarioLink() {
    const url = new URL(window.location.href);
    url.searchParams.delete("open");
    url.searchParams.delete("yes");
    url.searchParams.delete("no");
    url.searchParams.set("preview", "1");
    for (const id of active.accepted) { url.searchParams.append("yes", id); }
    for (const id of active.denied) { url.searchParams.append("no", id); }
    const link = url.toString();
    setShareLink(link);
    if (navigator.clipboard?.writeText) {
      void navigator.clipboard.writeText(link).catch(() => {
        // The visible, selectable text field remains available if clipboard access is blocked.
      });
    }
  }

  function focus(id: string) {
    setSearch("");
    setShareLink(null);
    update((next) => {
      next.set("goal", id);
      next.delete("open");
    });
  }

  function setAssumption(id: string, value: "true" | "false" | "clear") {
    if (preview) {
      setShareLink(null);
      update((next) => {
        const nextProfile = chooseBelief(profileFromQuery(next, known), id, value);
        next.set("preview", "1");
        next.delete("yes");
        next.delete("no");
        for (const entry of nextProfile.accepted) { next.append("yes", entry); }
        for (const entry of nextProfile.denied) { next.append("no", entry); }
      });
      return;
    }
    if (!saved) { return; }
    if ((value === "true" && saved.denied.includes(id)) ||
      (value === "false" && saved.accepted.includes(id))) {
      setPendingReversal({ id, value });
      return;
    }
    applySavedBelief(id, value);
  }

  function applySavedBelief(id: string, value: "true" | "false" | "clear") {
    if (!saved) { return; }
    if (value === "true" && !saved.accepted.includes(id) &&
      reviewNewBelief(new Set(saved.accepted), id, certifiedCores).cores.length) {
      setPending(id);
      return;
    }
    persist(chooseBelief(saved, id, value));
  }

  function toggle(path: string) {
    update((next) => {
      const current = next.has("open") ? next.getAll("open").filter((entry) => entry !== "-") : ["root"];
      const paths = toggleOpenPath(current, path);
      next.delete("open");
      // The sentinel lets a user collapse the initial root without it reopening on reload.
      if (!paths.length) { next.append("open", "-"); }
      else { for (const entry of paths) { next.append("open", entry); } }
    });
  }

  if (!model.statements[goal]) {
    return <p>No argument records are available for this build.</p>;
  }

  return <div className={styles.explorer}>
    <div className={styles.scenarioToolbar}>
      <div className={styles.propositionSearch}>
        <label htmlFor="find-proposition">Find a proposition to investigate or assume</label>
        <input id="find-proposition" type="search" value={search}
          onChange={(event) => setSearch(event.target.value)}
          placeholder="Search text or statement ID" autoComplete="off" />
        {query.length >= 2 ? <div className={styles.searchResults}>
          {choices.length ? <ul aria-label="Matching propositions">{choices.map((entry) =>
            <li key={entry.id}><button type="button" onClick={() => focus(entry.id)}>
              <strong>{entry.paraphrase}</strong>
              <span className={styles.searchDetail}><span>{shortId(entry.id)}</span>
                {relevance.completesGoalRoute.has(entry.id) ? <em>Completes a goal-path result route</em> :
                  relevance.goalDistance.has(entry.id) ? <em>On this goal&apos;s support path</em> : null}
                {scenario.accepted.has(entry.id) ? <em>Assumed true</em> :
                  scenario.denied.has(entry.id) ? <em>Assumed false</em> :
                    scenario.derived.has(entry.id) ? <em>Reached in this what-if</em> : null}
              </span>
            </button></li>)}</ul> : <p>No matching corpus proposition.</p>}
        </div> : null}
      </div>
      <button type="button" className={styles.reset} onClick={() => {
        setResultFilter("");
        update((next) => { next.delete("goal"); next.delete("open"); });
      }}>Reset tree view</button>
      <button type="button" className={styles.reset} onClick={copyScenarioLink}>Copy scenario link</button>
    </div>
    <section className={styles.beliefBanner} aria-label="Personal beliefs and scenario sharing">
      <div>
        <strong>{preview ? "Shared what-if preview · not saved" : "Your personal belief profile"}</strong>
        <p>{preview ? "These choices come from the URL. Nothing here changes your saved beliefs unless you explicitly replace them." :
          "Truth/False selections are private to this browser and saved locally, separate from Truth Core’s verified proposition statuses."}</p>
        {!storageAvailable ? <p className={styles.storageWarning}>Browser storage is unavailable. These choices may not survive a reload.</p> : null}
      </div>
      <div className={styles.beliefActions}>
        {preview ? <>
          <button type="button" onClick={clearPreview}>Return to saved beliefs</button>
          <button type="button" onClick={() => setConfirmReplace(true)} disabled={!saved}>Replace my saved beliefs with this preview</button>
        </> : <button type="button" disabled={!saved || !(saved.accepted.length + saved.denied.length)}
          onClick={() => setConfirmClear(true)}>Clear saved beliefs</button>}
      </div>
      {confirmReplace && preview ? <div className={styles.beliefConfirm} role="group" aria-label="Confirm replacing saved beliefs">
        <p>This replaces all your locally saved True/False selections with the preview, including any incompatible selections it contains.</p>
        {saved?.accepted.some((id) => !fromUrl.accepted.includes(id)) ? <div className={styles.replacementSummary}>
          <strong>Previously accepted propositions to withdraw</strong>
          <ul>{saved.accepted.filter((id) => !fromUrl.accepted.includes(id)).map((id) =>
            <li key={id}>{model.statements[id]?.paraphrase ?? id}</li>)}</ul>
        </div> : null}
        {saved?.denied.some((id) => !fromUrl.denied.includes(id)) ? <div className={styles.replacementSummary}>
          <strong>Previously rejected propositions to clear</strong>
          <ul>{saved.denied.filter((id) => !fromUrl.denied.includes(id)).map((id) =>
            <li key={id}>{model.statements[id]?.paraphrase ?? id}</li>)}</ul>
        </div> : null}
        <button type="button" onClick={() => { persist(fromUrl); clearPreview(); }}>Confirm replacement</button>
        <button type="button" onClick={() => setConfirmReplace(false)}>Cancel</button>
      </div> : null}
      {confirmClear && !preview ? <div className={styles.beliefConfirm} role="group" aria-label="Confirm clearing saved beliefs">
        <p>Remove all locally saved True/False selections from this browser?</p>
        <button type="button" onClick={() => { persist(EMPTY_BELIEFS); setConfirmClear(false); }}>Clear all saved selections</button>
        <button type="button" onClick={() => setConfirmClear(false)}>Cancel</button>
      </div> : null}
      {shareLink ? <div className={styles.shareLink}><label htmlFor="scenario-share-url">Shareable preview URL (select to copy)</label>
        <input id="scenario-share-url" value={shareLink} readOnly onFocus={(event) => event.target.select()} /></div> : null}
    </section>
    {pendingReversal ? <section className={styles.beliefReview} aria-label="Review reversing a saved belief">
      <h2>Replace an earlier belief?</h2>
      <p>You previously selected <strong>{pendingReversal.value === "true" ? "False" : "True"}</strong> for
        <strong> {model.statements[pendingReversal.id]?.paraphrase ?? pendingReversal.id}</strong>.
        Choosing {pendingReversal.value === "true" ? "True" : "False"} withdraws that earlier selection.</p>
      <p>Changing a personal selection is not a proof of either the proposition or its negation.</p>
      <div className={styles.reviewActions}>
        <button type="button" onClick={() => {
          const { id, value } = pendingReversal;
          setPendingReversal(null);
          applySavedBelief(id, value);
        }}>Withdraw earlier choice and continue</button>
        <button type="button" onClick={() => setPendingReversal(null)}>Keep my earlier choice</button>
      </div>
    </section> : null}
    {pending && pendingReview?.cores.length ? <ConflictReview key={pending}
      model={model} proposedId={pending} review={pendingReview}
      onRejectAndAccept={(ids) => { persist(chooseBelief(rejectBeliefs(saved ?? EMPTY_BELIEFS, ids), pending, "true")); setPending(null); }}
      onAcceptAnyway={() => { persist(chooseBelief(saved ?? EMPTY_BELIEFS, pending, "true")); setPending(null); }}
      onCancel={() => setPending(null)} /> : null}
    <div className={styles.mapKey}>
      <span><i data-status="established" /> Corpus-established</span>
      <span><i data-status="conditional" /> Recorded conditional result</span>
      <span><i data-status="open" /> Open premise</span>
      <span>Route readiness and True/False = hypothetical, not certified statuses</span>
    </div>
    <div className={styles.scenarioLayout}>
      <section className={styles.treePanel} aria-label="Single proposition tree">
        <div className={styles.panelHeading}><div>
          <span className={styles.eyebrow}>Focused proposition · all argument routes</span>
          <p>Each OR route contains all its AND premises. Routes follow your current what-if readiness; every branch remains expandable.</p>
        </div></div>
        <StatementBranch model={model} id={goal} selected={goal} expanded={expanded}
          onSelect={focus} onToggle={toggle} exhaustive
          scenario={scenario} relevance={relevance} onAssume={setAssumption} />
        <p className={styles.hint}>
          <Link href={"/statements/" + goal}>View this proposition&apos;s evidence</Link>
          {" · "}<Link href="/forest">Compare two conclusions instead</Link>
        </p>
      </section>
      <aside className={styles.scenarioPanel} aria-label="Scenario implications">
        <div className={styles.panelHeading}><div>
          <span className={styles.eyebrow}>What follows from these choices?</span>
          <p>Recorded result-bearing arguments are applied only when every ordinary premise is accepted or reached.</p>
        </div></div>
        <h2>{preview ? "Previewed choices" : "Saved beliefs"} ({scenario.accepted.size + scenario.denied.size})</h2>
        {selectedIds.length ? <ul className={styles.selectedAssumptions}>
          {selectedIds.map((id) => <li key={id}>
            <span><strong>{scenario.accepted.has(id) ? "True" : "False"}</strong> · {model.statements[id].paraphrase}</span>
            <button type="button" aria-label={"Clear assumption " + id} onClick={() => setAssumption(id, "clear")}>×</button>
          </li>)}
        </ul> : <p className={styles.hint}>Choose True or False on the tree, or find another proposition above.</p>}
        <section className={styles.certifiedSummary} aria-label="Certified incompatibility overview">
          <h2>Certified incompatibilities ({activeCores.length})</h2>
          {!hasCertifiedEvidence ? <p>Verified configuration evidence is unavailable in this build. Compatibility cannot be checked here.</p> :
            activeCores.length ? <>
              <p>These selected propositions jointly activate the following producer-verified incompatible cores. Each certificate is specific to its stated semantic profile.</p>
              <ul>{activeCores.map((core) => <li key={core.key}>
                <strong>{core.caseLabel ?? core.caseId}</strong> · {core.statementIds.map((id) => model.statements[id]?.paraphrase ?? id).join(" + ")}
                <span>{core.profile} · {core.resultIds.map((id, index) => <span key={id}>
                  {index ? ", " : ""}<Link href={"/results/" + id}>{id}</Link></span>)}</span>
              </li>)}</ul>
            </> : <p>No selected set activates a displayed certified core. This does not establish that your selections are compatible.</p>}
        </section>
        {scenario.conflicts.size > 0 ? <section className={styles.conflicts} aria-label="Scenario conflicts">
          <h2>Conflicts ({scenario.conflicts.size})</h2>
          <p>A denied statement also follows from accepted premises through a recorded result. This selection is in tension; no further conclusions are propagated through that denial.</p>
          <ul>{[...scenario.conflicts.entries()].map(([id, routes]) => <li key={id}>
            <button type="button" onClick={() => focus(id)}>{model.statements[id].paraphrase}</button>
            <span> via {routes.join(", ")}</span>
          </li>)}</ul>
        </section> : null}
        <div className={styles.scenarioResultsHeader}>
          <h2>Derived implications ({scenario.derived.size})</h2>
          <p className={styles.hint}>Closest to the focused goal first; all are hypothetical consequences of recorded result routes.</p>
          <label htmlFor="find-consequence">Filter</label>
          <input id="find-consequence" type="search" value={resultFilter}
            onChange={(event) => setResultFilter(event.target.value)} placeholder="Filter implications" />
        </div>
        {matches.length ? <ol className={styles.implications}>
          {matches.map(([id, routes]) => <li key={id}>
            <button type="button" onClick={() => focus(id)}>
              <strong>{model.statements[id].paraphrase}</strong>
              <span>{id}</span>
            </button>
            <span>via {routes.length} recorded route{routes.length === 1 ? "" : "s"}
              {routes[0] ? " · " + routes[0] : ""}</span>
            {routes[0] && model.arguments[routes[0]]?.resultIds[0] ?
              <Link href={"/results/" + model.arguments[routes[0]].resultIds[0]}>Inspect result</Link> : null}
          </li>)}
        </ol> : <p className={styles.hint}>
          {resultFilter ? "No derived implications match this filter." : "No additional result follows yet. Try accepting the remaining premises of an argument."}
        </p>}
        <p className={styles.warning}>
          This is hypothetical reachability through recorded result routes—not a new Lean proof or a change to Truth Core&apos;s established, refuted, or open statuses.
          Unselected statements remain unknown. Research links, result-free arguments, and zero-premise results with undisplayed commitments do not automatically derive conclusions;
          denying a statement does not prove its negation.
        </p>
      </aside>
    </div>
  </div>;
}
