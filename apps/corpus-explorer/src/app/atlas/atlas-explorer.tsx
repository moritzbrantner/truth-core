"use client";

import Link from "next/link";
import { useRouter, useSearchParams } from "next/navigation";
import { useMemo, useState } from "react";

import { selectedConfiguration } from "@/lib/configuration-selection";
import type { VerifiedConfigurationBundle, VerifiedConfigurationCase } from "@/lib/verified-configurations";

import {
  certifiedCores, certifiedMosaic, frontierTiles, routeImpact,
  type AtlasCore, type AtlasModel, type AtlasMosaicCell, type AtlasPremise,
} from "./atlas-model";
import styles from "./atlas.module.css";

type View = "cores" | "mosaic" | "routes" | "frontier" | "impact";
type Registration = { id: string; semantics: VerifiedConfigurationCase["semantics"]; scope: string };
type Props = {
  model: AtlasModel;
  cases: VerifiedConfigurationCase[];
  producer: VerifiedConfigurationBundle["producer"] | null;
  registrations: Registration[];
};

const views: Array<{ id: View; number: string; label: string; description: string }> = [
  { id: "cores", number: "01", label: "Incompatibilities", description: "Certified sets of jointly incompatible propositions" },
  { id: "mosaic", number: "02", label: "Configuration space", description: "Every bounded assumption selection, classified by the producer" },
  { id: "routes", number: "03", label: "Proof routes", description: "Alternative conditional routes to the root proposition" },
  { id: "frontier", number: "04", label: "Frontier treemap", description: "Which open premises sit where in the research frontier" },
  { id: "impact", number: "05", label: "Impact waves", description: "Recorded dependency reach when a premise is challenged" },
];

function compactId(id: string): string {
  return id.replace(/^STMT-/, "").replace(/^CATHOLICISM-/, "").replaceAll("-", " ").toLowerCase();
}

function radial(index: number, count: number, radius: number, centerX = 440, centerY = 255) {
  const angle = -Math.PI / 2 + index * 2 * Math.PI / Math.max(count, 1);
  return { x: centerX + Math.cos(angle) * radius, y: centerY + Math.sin(angle) * radius };
}

function StatusMark({ status }: { status: AtlasMosaicCell["status"] }) {
  const className = status === "verified incompatible" ? styles.incompatible : status === "model witnessed" ? styles.witnessed : styles.unresolved;
  return <span className={`${styles.statusMark} ${className}`}>{status}</span>;
}

function EmptyCertification({ registrations }: { registrations: Registration[] }) {
  return <section className={styles.emptyState} aria-label="Certification unavailable">
    <span className={styles.emptySymbol}>∅</span>
    <h3>Certification unavailable in this build</h3>
    <p>The verified configuration report is missing. Registered cases alone do not establish that a set is incompatible or satisfiable. The GitHub Pages deployment produces a fresh report before building the atlas.</p>
    {registrations.length > 0 ? <div className={styles.registrationList}>
      <span className={styles.microLabel}>Registered cases · verification required</span>
      {registrations.map((entry) => <Link href={`/configurations/${entry.id}`} key={entry.id}>{compactId(entry.id)} <span>↗</span></Link>)}
    </div> : null}
  </section>;
}

function CaseSelector({ cases, selected, onChange }: { cases: VerifiedConfigurationCase[]; selected: string; onChange: (id: string) => void }) {
  return <label className={styles.selectLabel}>Formal case / semantic profile
    <select value={selected} onChange={(event) => onChange(event.target.value)}>
      {cases.map((entry) => <option value={entry.id} key={entry.id}>{compactId(entry.id)} · {entry.semantics.id}</option>)}
    </select>
  </label>;
}

function Constellation({ cores, selected, onSelect }: { cores: AtlasCore[]; selected: AtlasCore; onSelect: (key: string) => void }) {
  const propositions = [...new Set(cores.flatMap((core) => core.statement_ids))].sort();
  const statementPoints = new Map(propositions.map((id, index) => [id, radial(index, propositions.length, propositions.length < 5 ? 176 : 212)]));
  const corePoints = cores.map((_, index) => cores.length === 1 ? { x: 440, y: 255 } : radial(index, cores.length, Math.min(122, 42 + cores.length * 15)));
  return <div className={styles.diagramFrame}>
    <div className={styles.diagramHeading}><span>Certified core / statement incidence</span><span>{cores.length} cores · {propositions.length} unique statements</span></div>
    <svg className={styles.constellation} viewBox="0 0 880 510" role="group" aria-label="Incompatible cores connected to their member statements; choose a core using the diagram or the list">
      {cores.flatMap((core, coreIndex) => core.statement_ids.map((id) => {
        const point = statementPoints.get(id);
        if (!point) { return null; }
        const isActive = selected.key === core.key;
        return <line key={`${core.key}:${id}`} x1={corePoints[coreIndex].x} y1={corePoints[coreIndex].y}
          x2={point.x} y2={point.y} className={isActive ? styles.activeEdge : styles.mutedEdge} />;
      }))}
      {propositions.map((id, index) => {
        const point = statementPoints.get(id)!;
        const active = selected.statement_ids.includes(id);
        return <g key={id}>
          <circle cx={point.x} cy={point.y} r={active ? 18 : 14} className={active ? styles.activeProposition : styles.proposition} />
          <text x={point.x} y={point.y + 4} textAnchor="middle" className={styles.nodeText}>P{index + 1}</text>
          <title>{id}</title>
        </g>;
      })}
      {cores.map((core, index) => {
        const point = corePoints[index];
        return <g key={core.key} role="button" tabIndex={0} aria-label={`Select certified core ${index + 1}`}
          className={styles.coreNode} onClick={() => onSelect(core.key)}
          onKeyDown={(event) => { if (event.key === "Enter" || event.key === " ") { event.preventDefault(); onSelect(core.key); } }}>
          <circle cx={point.x} cy={point.y} r={selected.key === core.key ? 31 : 25} className={selected.key === core.key ? styles.activeCore : styles.inactiveCore} />
          <text x={point.x} y={point.y + 5} textAnchor="middle" className={styles.coreText}>C{index + 1}</text>
          <title>Core {index + 1}: {core.statement_ids.length} jointly incompatible statements</title>
        </g>;
      })}
    </svg>
    <p className={styles.diagramFoot}>A core is a set, not a pairwise conflict: the connections mean membership. Two propositions connected to one core need not contradict each other alone.</p>
  </div>;
}

function CoreView({ model, cases, producer, registrations, selectedCase, changeCase, selectedCoreKey, selectCore }: Props & {
  selectedCase: VerifiedConfigurationCase | null;
  changeCase: (id: string) => void;
  selectedCoreKey: string | null;
  selectCore: (key: string) => void;
}) {
  if (!producer || !selectedCase) { return <EmptyCertification registrations={registrations} />; }
  const cores = certifiedCores(selectedCase);
  const selected = cores.find((core) => core.key === selectedCoreKey) ?? cores[0];
  return <div className={styles.viewBody}>
    <div className={styles.viewToolbar}>
      <CaseSelector cases={cases} selected={selectedCase.id} onChange={changeCase} />
      <span className={styles.provenance}>Freshly verified · <span title={producer.trust}>{producer.source_head.slice(0, 10)}</span></span>
    </div>
    {selected ? <>
      <Constellation cores={cores} selected={selected} onSelect={selectCore} />
      <div className={styles.detailColumns}>
        <section className={styles.panel}>
          <div className={styles.panelHeading}><span>Core index</span><span>{cores.length} certificates</span></div>
          <div className={styles.coreIndex}>{cores.map((core, index) => <button type="button" className={`${styles.coreIndexButton} ${selected.key === core.key ? styles.activeIndex : ""}`}
            onClick={() => selectCore(core.key)} key={core.key} aria-pressed={selected.key === core.key}>
            <span className={styles.indexCircle}>C{index + 1}</span><span>{core.statement_ids.length} propositions<span className={styles.indexSecondary}>{core.result_ids.length} Lean result{core.result_ids.length === 1 ? "" : "s"}</span></span>
          </button>)}</div>
        </section>
        <section className={styles.panel} aria-label="Selected core details">
          <div className={styles.panelHeading}><span>Selected incompatible set</span><StatusMark status="verified incompatible" /></div>
          <p className={styles.panelNote}>{selected.minimality}</p>
          <ol className={styles.statementList}>{selected.statement_ids.map((id, index) => <li key={id}>
            <span className={styles.statementNumber}>P{[...new Set(cores.flatMap((core) => core.statement_ids))].sort().indexOf(id) + 1 || index + 1}</span>
            <span><Link href={`/statements/${id}`} className={styles.recordLink}>{id}</Link><span className={styles.statementParaphrase}>{model.labels[id] ?? id}</span></span>
          </li>)}</ol>
          <div className={styles.proofLinks}><span>Verified results</span>{selected.result_ids.map((id) => <Link href={`/results/${id}`} key={id}>{id}</Link>)}</div>
          <details className={styles.evidenceDetails}><summary>Single-premise removal evidence</summary>
            <ul>{selected.removal_evidence.map((entry) => <li key={entry.removed_statement_id}><strong>{entry.removed_statement_id}</strong> · {entry.model_ids.length ? entry.model_ids.join(", ") : "No matching certified witness"}</li>)}</ul>
          </details>
        </section>
      </div>
    </> : <section className={styles.emptyState}><h3>No certified incompatible core for this semantic profile</h3><p>This is an absence of a recorded certificate, not a satisfiability result.</p></section>}
    <p className={styles.scopeNote}>Profile: {selectedCase.semantics.logic} / {selectedCase.semantics.frame} / {selectedCase.semantics.domain}. <Link href={`/configurations/${selectedCase.id}`}>Inspect semantic bindings and certificates ↗</Link></p>
  </div>;
}

function MosaicView({ cases, producer, registrations, selectedCase, changeCase, maskParam, selectMask }: Pick<Props, "cases" | "producer" | "registrations"> & {
  selectedCase: VerifiedConfigurationCase | null;
  changeCase: (id: string) => void;
  maskParam: string | null;
  selectMask: (mask: number) => void;
}) {
  const cells = useMemo(() => selectedCase ? certifiedMosaic(selectedCase) : [], [selectedCase]);
  if (!producer || !selectedCase) { return <EmptyCertification registrations={registrations} />; }
  const dimensions = selectedCase.assumption_space.statement_ids;
  const requestedMask = maskParam === null ? NaN : Number(maskParam);
  const defaultCell = cells.find((cell) => cell.status === "verified incompatible") ?? cells.find((cell) => cell.status === "model witnessed") ?? cells[0];
  const selected = cells.find((cell) => cell.mask === requestedMask) ?? defaultCell;
  const columns = Math.ceil(Math.sqrt(cells.length));
  const counts = {
    "verified incompatible": cells.filter((cell) => cell.status === "verified incompatible").length,
    "model witnessed": cells.filter((cell) => cell.status === "model witnessed").length,
    unresolved: cells.filter((cell) => cell.status === "unresolved").length,
  };
  const assessment = selected ? selectedConfiguration(selectedCase.assumption_space, selected.statementIds) : null;
  const selectedReport = assessment?.terminal?.report;
  const dossierQuery = new URLSearchParams({ set: "custom" });
  for (const id of selected?.statementIds ?? []) { dossierQuery.append("premise", id); }
  return <div className={styles.viewBody}>
    <div className={styles.viewToolbar}>
      <CaseSelector cases={cases} selected={selectedCase.id} onChange={changeCase} />
      <span className={styles.provenance}>{dimensions.length} Boolean dimensions · {cells.length} selections</span>
    </div>
    <div className={styles.mosaicLayout}>
      <section className={styles.panel} aria-label="Certified configuration mosaic">
        <div className={styles.panelHeading}><span>Selection landscape</span><span>Gray-code order</span></div>
        <p className={styles.panelNote}>Each square is one exact assumption selection. Neighboring squares in reading order change one assumption. Color is the producer’s certified status, not a probability.</p>
        <div className={styles.mosaic} style={{ gridTemplateColumns: `repeat(${columns}, minmax(0, 1fr))` }}>
          {cells.map((cell) => <button type="button" key={cell.mask} title={`${cell.statementIds.length} selected · ${cell.status}`}
            aria-label={`Selection ${cell.mask}: ${cell.statementIds.length} assumptions; ${cell.status}`}
            aria-pressed={selected?.mask === cell.mask} onClick={() => selectMask(cell.mask)}
            className={`${styles.mosaicCell} ${cell.status === "verified incompatible" ? styles.cellIncompatible : cell.status === "model witnessed" ? styles.cellWitnessed : styles.cellUnresolved} ${selected?.mask === cell.mask ? styles.selectedCell : ""}`} />)}
        </div>
        <div className={styles.mosaicLegend}>{(["verified incompatible", "model witnessed", "unresolved"] as const).map((status) => <div key={status}>
          <StatusMark status={status} /><strong>{counts[status]}</strong><span>{(100 * counts[status] / Math.max(cells.length, 1)).toFixed(0)}%</span>
        </div>)}</div>
      </section>
      <section className={styles.panel} aria-label="Selected configuration details">
        <div className={styles.panelHeading}><span>Selection / {selected?.mask ?? "—"}</span>{selected ? <StatusMark status={selected.status} /> : null}</div>
        <p className={styles.panelNote}>Toggle assumptions to examine another pre-certified selection.</p>
        <fieldset className={styles.assumptionChoices}><legend className="sr-only">Selected assumptions</legend>
          {dimensions.map((id, bit) => <label key={id} className={styles.assumptionChoice}>
            <input type="checkbox" checked={Boolean(selected && (selected.mask & (1 << bit)))} onChange={() => selectMask((selected?.mask ?? 0) ^ (1 << bit))} />
            <span><span>{compactId(id)}</span><small>{id}</small></span>
          </label>)}
        </fieldset>
        {selectedReport ? <div className={styles.selectionOutcome}>
          {selectedReport.status === "verified incompatible" ? <><p>At least one certified incompatible core is contained in this selection.</p>
            {selectedReport.incompatible_cores.map((core) => <p key={core.result_id}><Link href={`/results/${core.result_id}`}>{core.result_id}</Link> · {core.statement_ids.length} members</p>)}
          </> : selectedReport.status === "model witnessed" ? <><p>A recorded model satisfies all selected formulas in this semantic profile.</p>
            {selectedReport.model_ids.map((id) => <p className={styles.mono} key={id}>{id}</p>)}</> : <p>{selectedReport.unresolved_reason ?? "No certificate or model witness recorded for this selection."}</p>}
          {selectedReport.core_composition.truncated ? <p>Core composition was bounded; completeness remains unresolved.</p> : null}
        </div> : null}
        <Link className={styles.primaryAction} href={`/configurations/${selectedCase.id}?${dossierQuery.toString()}`}>Open exact certificates and model evaluations ↗</Link>
      </section>
    </div>
    <p className={styles.scopeNote}>Enumerates a bounded formal assumption vocabulary, not all conceivable metaphysical worlds. {selectedCase.assumption_space.limits.note} · Source {producer.source_head.slice(0, 10)}</p>
  </div>;
}

function RouteView({ model, selectedRouteId, selectRoute }: { model: AtlasModel; selectedRouteId: string | null; selectRoute: (id: string) => void }) {
  const routes = model.routes;
  const selected = routes.find((route) => route.argument_id === selectedRouteId) ?? routes.find((route) => route.designated) ?? routes[0];
  const max = Math.max(1, ...routes.map((route) => route.cost));
  const premiseDepth = new Map(model.premises.map((item) => [item.id, item.depth]));
  return <div className={styles.viewBody}>
    <div className={styles.metricStrip}>
      <div><span>Recorded root routes</span><strong>{routes.length}</strong></div>
      <div><span>Lowest unestablished-leaf cost</span><strong>{routes.length ? Math.min(...routes.map((route) => route.cost)) : 0}</strong></div>
      <div><span>Root proposition</span><strong className={styles.metricWord}>{model.establishedRoot ? "Established" : "Not established"}</strong></div>
    </div>
    <div className={styles.routeLayout}>
      <section className={styles.panel} aria-label="Compare conditional proof routes">
        <div className={styles.panelHeading}><span>Alternative routes / open premise burden</span><span>{routes.length} recorded</span></div>
        <div className={styles.barKey}><span><i className={styles.bareSwatch} /> Bare open</span><span><i className={styles.sourcedSwatch} /> Sourced open</span><span><i className={styles.unestablishedSwatch} /> Proved, unestablished</span></div>
        <div className={styles.routeRows}>{routes.map((route, index) => <button type="button" className={`${styles.routeRow} ${selected?.argument_id === route.argument_id ? styles.selectedRoute : ""}`}
          key={route.argument_id} aria-pressed={selected?.argument_id === route.argument_id} onClick={() => selectRoute(route.argument_id)}>
          <span className={styles.routeIndex}>{String(index + 1).padStart(2, "0")}</span>
          <span className={styles.routeRowBody}><span className={styles.routeName}>{compactId(route.argument_id)}</span>
            <span className={styles.routeBarTrack}><span className={styles.routeBare} style={{ width: `${100 * route.bare / max}%` }} /><span className={styles.routeSourced} style={{ width: `${100 * route.sourced / max}%` }} /><span className={styles.routeUnestablished} style={{ width: `${100 * route.provedUnestablished / max}%` }} /></span>
          </span>
          <strong className={styles.routeCost}>{route.cost}</strong>
        </button>)}</div>
        <p className={styles.panelNote}>Bars count distinct unestablished route leaves. Some are open premises; others have conditional proofs but are not established. Lower cost means fewer obligations on this measure, not a stronger or truer conclusion.</p>
      </section>
      {selected ? <section className={styles.panel} aria-label="Selected proof route">
        <div className={styles.panelHeading}><span>Selected route</span><span>{selected.cheapest ? "Lowest cost" : selected.designated ? "Designated" : "Alternative"}</span></div>
        <h3 className={styles.routeTitle}>{compactId(selected.argument_id)}</h3>
        <p className={styles.panelNote}>{selected.label}</p>
        <div className={styles.routeSummary}><div><strong>{selected.cost}</strong><span>route leaves</span></div><div><strong>{selected.bare}</strong><span>bare</span></div><div><strong>{selected.sourced}</strong><span>sourced</span></div><div><strong>{selected.provedUnestablished}</strong><span>proved, unestablished</span></div></div>
        <p className={styles.routeCaveat}>{selected.verified ? "Verified formal result" : "Formal verification not recorded"} · {selected.transcription ? "transcription-only" : "conditional derivation"} · {selected.proved_unestablished_statement_ids.length} proved but unestablished intermediates.</p>
        <Link href={model.argumentTargets[selected.argument_id]} className={styles.primaryAction}>Inspect argument and inferences ↗</Link>
        <details className={styles.evidenceDetails}><summary>Inspect all {selected.open_premise_statement_ids.length} route leaves</summary>
          <ul className={styles.detailPremises}>{selected.open_premise_statement_ids.map((id) => <li key={id}><span className={premiseDepth.get(id) === "bare" ? styles.bareBadge : premiseDepth.get(id) === "sourced" ? styles.sourcedBadge : styles.unestablishedBadge}>{premiseDepth.get(id) ?? "proved, unestablished"}</span><Link href={`/statements/${id}`}>{id}</Link></li>)}</ul>
        </details>
      </section> : null}
    </div>
  </div>;
}

function FrontierView({ model, selectedGroup, selectGroup }: { model: AtlasModel; selectedGroup: string | null; selectGroup: (id: string) => void }) {
  const [filter, setFilter] = useState("");
  const tiles = useMemo(() => frontierTiles(model.premises), [model.premises]);
  const active = tiles.find((tile) => tile.id === selectedGroup) ?? tiles[0];
  const groups = [{ id: "root", label: "Reaches root", entries: tiles.slice(0, 2) }, { id: "other", label: "Other open premises", entries: tiles.slice(2) }];
  const filtered = active.premises.filter((premise) => `${premise.id} ${premise.label}`.toLowerCase().includes(filter.toLowerCase()));
  const sorted = [...filtered].sort((a, b) => b.dependentStatements.length - a.dependentStatements.length || a.id.localeCompare(b.id));
  return <div className={styles.viewBody}>
    <div className={styles.metricStrip}>
      <div><span>Open premise frontier</span><strong>{model.premises.length}</strong></div>
      <div><span>Root-reaching open</span><strong>{model.premises.filter((item) => item.rootReaching).length}</strong></div>
      <div><span>With source claims</span><strong>{model.premises.filter((item) => item.depth === "sourced").length}</strong></div>
    </div>
    <section className={styles.panel} aria-label="Open-premise treemap">
      <div className={styles.panelHeading}><span>Disjoint partitions of the open frontier</span><span>Area = count</span></div>
      <div className={styles.treeMap}>{groups.map((group) => {
        const total = group.entries.reduce((sum, tile) => sum + tile.count, 0);
        return <div key={group.id} className={styles.treeGroup} style={{ flexGrow: total || 1 }}>
          <span className={styles.treeGroupTitle}>{group.label} · {total}</span>
          <div className={styles.treeGroupTiles}>{group.entries.map((tile) => <button type="button" key={tile.id}
            className={`${styles.treeTile} ${tile.depth === "bare" ? styles.treeBare : styles.treeSourced} ${active.id === tile.id ? styles.treeActive : ""}`}
            style={{ flexGrow: tile.count || 0.01 }} onClick={() => selectGroup(tile.id)} aria-pressed={active.id === tile.id}>
            <strong>{tile.count}</strong><span>{tile.depth}</span>
          </button>)}</div>
        </div>;
      })}</div>
      <p className={styles.diagramFoot}>Each open premise appears exactly once. “Sourced” means it has recorded source claims; it does not mean justified or established. “Reaches root” means a recorded dependency path.</p>
    </section>
    <section className={styles.panel} aria-label="Selected frontier partition">
      <div className={styles.panelHeading}><span>{active.title}</span><span>{active.count} open premises</span></div>
      <label className={styles.searchLabel}>Find within partition<input type="search" value={filter} onChange={(event) => setFilter(event.target.value)} placeholder="Statement ID or text…" /></label>
      <ul className={styles.frontierList}>{sorted.slice(0, 18).map((premise) => <li key={premise.id}>
        <Link href={`/statements/${premise.id}`}>{premise.id}</Link>
        <p>{premise.label}</p>
        <span>{premise.dependentStatements.length} recorded downstream statements · {premise.objections.length} objections</span>
      </li>)}</ul>
      <p className={styles.listFoot}>Showing {Math.min(sorted.length, 18)} of {filtered.length} matching premises. <Link href="/">Open the complete frontier ↗</Link></p>
    </section>
  </div>;
}

function ImpactWaves({ premise, model }: { premise: AtlasPremise; model: AtlasModel }) {
  const affectedRoutes = model.routes.filter((route) => routeImpact(route, premise.id));
  const rings = [
    { label: "Arguments", count: premise.dependentArguments.length, radius: 92, className: styles.impactArgument },
    { label: "Statements", count: premise.dependentStatements.length, radius: 149, className: styles.impactStatement },
    { label: "Root routes", count: affectedRoutes.length, radius: 201, className: styles.impactRoute },
  ];
  return <div className={styles.waveFrame}>
    <svg viewBox="0 0 720 450" role="img" aria-label={`${premise.id} reaches ${premise.dependentArguments.length} arguments and ${premise.dependentStatements.length} statements in the recorded dependency graph; ${affectedRoutes.length} root routes contain it as an open leaf`}>
      {rings.map((ring) => <g key={ring.label}>
        <circle cx="250" cy="223" r={ring.radius} className={styles.impactRing} />
        {Array.from({ length: Math.min(20, ring.count) }, (_, index) => {
          const point = radial(index, Math.min(20, ring.count), ring.radius, 250, 223);
          return <circle key={index} cx={point.x} cy={point.y} r="4" className={ring.className} />;
        })}
      </g>)}
      <circle cx="250" cy="223" r="43" className={styles.impactCenter} />
      <text x="250" y="218" textAnchor="middle" className={styles.impactCenterTop}>ONE</text>
      <text x="250" y="235" textAnchor="middle" className={styles.impactCenterBottom}>PREMISE</text>
      {rings.map((ring, index) => <g key={ring.label}>
        <text x="488" y={128 + index * 95} className={styles.impactCount}>{ring.count}</text>
        <text x="488" y={149 + index * 95} className={styles.impactLabel}>{ring.label}</text>
      </g>)}
    </svg>
    <p className={styles.diagramFoot}>Concentric bands show categories of recorded reachability, not causal distance or a measure of logical necessity. Dots are capped at 20 per band; the numbers are exact.</p>
  </div>;
}

function ImpactView({ model, selectedPremiseId, selectPremise }: { model: AtlasModel; selectedPremiseId: string | null; selectPremise: (id: string) => void }) {
  const ranked = useMemo(() => [...model.premises].sort((a, b) =>
    Number(b.rootReaching) - Number(a.rootReaching) || b.dependentStatements.length - a.dependentStatements.length || a.id.localeCompare(b.id)), [model.premises]);
  const selected = ranked.find((item) => item.id === selectedPremiseId) ?? ranked[0];
  if (!selected) { return <p>No recorded open premises.</p>; }
  const affectedRoutes = model.routes.filter((route) => routeImpact(route, selected.id));
  const unaffectedRoutes = model.routes.filter((route) => !routeImpact(route, selected.id));
  return <div className={styles.viewBody}>
    <div className={styles.viewToolbar}>
      <label className={styles.selectLabel}>Challenge an open premise
        <select value={selected.id} onChange={(event) => selectPremise(event.target.value)}>
          {ranked.map((item) => <option key={item.id} value={item.id}>{compactId(item.id)} · {item.dependentStatements.length} downstream</option>)}
        </select>
      </label>
      <Link href={`/statements/${selected.id}`} className={styles.provenance}>Open proposition ↗</Link>
    </div>
    <div className={styles.impactHeading}><p className={styles.microLabel}>Hypothetical challenge / recorded dependencies</p><h3>{selected.label}</h3>
      <p>Suppose this premise could no longer support its dependent arguments. What recorded paths would need reconsideration?</p>
    </div>
    <ImpactWaves premise={selected} model={model} />
    <div className={styles.detailColumns}>
      <section className={styles.panel}>
        <div className={styles.panelHeading}><span>Recorded downstream support</span><span>{selected.dependentArguments.length + selected.dependentStatements.length} records to inspect</span></div>
        <details className={styles.evidenceDetails} open><summary>{selected.dependentArguments.length} dependent arguments</summary><ul>
          {selected.dependentArguments.map((id) => <li key={id}><Link href={model.argumentTargets[id]}>{id}</Link></li>)}
        </ul></details>
        <details className={styles.evidenceDetails}><summary>{selected.dependentStatements.length} downstream conclusions</summary><ul>
          {selected.dependentStatements.map((id) => <li key={id}><Link href={`/statements/${id}`}>{id}</Link></li>)}
        </ul></details>
      </section>
      <section className={styles.panel}>
        <div className={styles.panelHeading}><span>Recorded root-route exposure</span><span>{affectedRoutes.length} / {model.routes.length}</span></div>
        <div className={styles.impactRouteBars}><span style={{ width: `${100 * affectedRoutes.length / Math.max(model.routes.length, 1)}%` }} /></div>
        <p className={styles.panelNote}>Contains this premise as a distinct open leaf:</p>
        {affectedRoutes.length ? <ul className={styles.impactRouteList}>{affectedRoutes.map((route) => <li key={route.argument_id}><span className={styles.affectedDot} /><Link href={model.argumentTargets[route.argument_id]}>{compactId(route.argument_id)}</Link></li>)}</ul> : <p className={styles.panelNote}>None of the recorded root routes contains this open leaf.</p>}
        <p className={styles.panelNote}>{unaffectedRoutes.length} other recorded route{unaffectedRoutes.length === 1 ? " does" : "s do"} not include this premise as an open leaf. That does not show those routes are independent of every related assumption.</p>
      </section>
    </div>
    <p className={styles.scopeNote}>A challenge to one premise is not a refutation of a conclusion. This is a dependency-impact preview, not a fresh Lean proof, automatic premise rejection, or an establishment of an alternative route.</p>
  </div>;
}

export function AtlasExplorer({ model, cases, producer, registrations }: Props) {
  const query = useSearchParams();
  const router = useRouter();
  const requestedView = query.get("view");
  const view: View = views.some((entry) => entry.id === requestedView) ? requestedView as View : "cores";
  const selectedCase = cases.find((entry) => entry.id === query.get("case")) ??
    (view === "cores" ? cases.find((entry) => certifiedCores(entry).length > 0) : null) ?? cases[0] ?? null;

  function change(changes: Record<string, string | null>) {
    const next = new URLSearchParams(query.toString());
    for (const [key, value] of Object.entries(changes)) {
      if (value === null) { next.delete(key); } else { next.set(key, value); }
    }
    router.replace(`/atlas?${next.toString()}`, { scroll: false });
  }

  const commonCase = { model, cases, producer, registrations, selectedCase, changeCase: (id: string) => change({ case: id, core: null, mask: null }) };
  return <div className={styles.atlasRoot}>
    <nav aria-label="Atlas visualizations" className={styles.tabs}>
      {views.map((entry) => <button type="button" key={entry.id} className={`${styles.tab} ${entry.id === view ? styles.activeTab : ""}`}
        aria-current={entry.id === view ? "page" : undefined} onClick={() => change({ view: entry.id })}>
        <span>{entry.number}</span><strong>{entry.label}</strong>
      </button>)}
    </nav>
    <div className={styles.viewIntro}><p>{views.find((entry) => entry.id === view)?.description}</p><span>VIEW {views.find((entry) => entry.id === view)?.number} / 05</span></div>
    {view === "cores" ? <CoreView {...commonCase} selectedCoreKey={query.get("core")} selectCore={(key) => change({ core: key })} /> : null}
    {view === "mosaic" ? <MosaicView cases={cases} producer={producer} registrations={registrations} selectedCase={selectedCase}
      changeCase={commonCase.changeCase} maskParam={query.get("mask")} selectMask={(mask) => change({ mask: String(mask) })} /> : null}
    {view === "routes" ? <RouteView model={model} selectedRouteId={query.get("route")} selectRoute={(id) => change({ route: id })} /> : null}
    {view === "frontier" ? <FrontierView model={model} selectedGroup={query.get("group")} selectGroup={(id) => change({ group: id })} /> : null}
    {view === "impact" ? <ImpactView model={model} selectedPremiseId={query.get("premise")} selectPremise={(id) => change({ premise: id })} /> : null}
  </div>;
}
