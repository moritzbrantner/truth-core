"use client";

import { Background, Controls, MarkerType, ReactFlow, type Edge, type Node } from "@xyflow/react";
import { usePathname, useRouter, useSearchParams } from "next/navigation";
import { useEffect, useMemo, useRef } from "react";

import {
  AXIOMS,
  DEFAULT_VALUATION,
  MODAL_CUBE_EDGES,
  MODAL_SYSTEMS,
  WORLDS,
  buildWitnessFrame,
  detectFrameConditions,
  impliedAxioms,
  modalTruthAt,
  parseExplorerState,
  requiredConditions,
  serializeExplorerState,
  type ExplorerState,
  type FrameCondition,
  type ModalSystemId,
  type WorldId,
} from "./modal-cube";

const conditionLabels = {
  serial: "serial",
  reflexive: "reflexive",
  symmetric: "symmetric",
  transitive: "transitive",
  euclidean: "Euclidean",
} as const;

const frameConditions: FrameCondition[] = [
  "serial",
  "reflexive",
  "symmetric",
  "transitive",
  "euclidean",
];

function truthLabel(value: boolean) {
  return value ? "true" : "false";
}

export function ModalExplorer() {
  const pathname = usePathname();
  const router = useRouter();
  const searchParams = useSearchParams();
  const state = useMemo(() => parseExplorerState(searchParams), [searchParams]);
  const { systemId: selectedSystemId, worldId: currentWorld, valuation } = state;

  // Compose updates issued before the previous router.replace commits, so rapid
  // interactions build on each other instead of on the last rendered URL.
  const pendingState = useRef<ExplorerState | null>(null);
  useEffect(() => {
    pendingState.current = null;
  }, [searchParams]);

  const updateState = (patch: (current: ExplorerState) => Partial<ExplorerState>) => {
    const base = pendingState.current ?? state;
    const next = { ...base, ...patch(base) };
    pendingState.current = next;
    const queryString = serializeExplorerState(next).toString();
    router.replace(queryString ? `${pathname}?${queryString}` : pathname, { scroll: false });
  };
  const setSelectedSystemId = (systemId: ModalSystemId) => updateState(() => ({ systemId }));
  const setCurrentWorld = (worldId: WorldId) => updateState(() => ({ worldId }));
  const setValuation = (next: Record<WorldId, boolean>) => updateState(() => ({ valuation: next }));

  const system = MODAL_SYSTEMS.find((candidate) => candidate.id === selectedSystemId) ?? MODAL_SYSTEMS[0];
  const axioms = useMemo(() => impliedAxioms(system), [system]);
  const required = useMemo(() => requiredConditions(system), [system]);
  const witnessEdges = useMemo(() => buildWitnessFrame(system), [system]);
  const detected = useMemo(() => detectFrameConditions(witnessEdges), [witnessEdges]);
  const truth = useMemo(
    () => modalTruthAt(currentWorld, witnessEdges, valuation),
    [currentWorld, valuation, witnessEdges],
  );

  const cubeNodes = useMemo<Node[]>(
    () =>
      MODAL_SYSTEMS.map((candidate) => ({
        id: candidate.id,
        position: candidate.position,
        data: {
          label: (
            <div className="text-left">
              <strong className="block font-serif text-lg">{candidate.name}</strong>
              <span className="text-[11px] text-[var(--muted)]">
                {candidate.explicitAxioms.length ? `+ ${candidate.explicitAxioms.join(" ")}` : "base logic"}
              </span>
            </div>
          ),
        },
        draggable: false,
        selectable: true,
        style: {
          width: 116,
          borderColor: candidate.id === selectedSystemId ? "var(--accent)" : "var(--line-strong)",
          borderWidth: candidate.id === selectedSystemId ? 2 : 1,
          background: candidate.id === selectedSystemId ? "var(--callout)" : "var(--paper)",
          color: "var(--ink)",
          borderRadius: 12,
          padding: 10,
        },
      })),
    [selectedSystemId],
  );

  const cubeEdges = useMemo<Edge[]>(
    () =>
      MODAL_CUBE_EDGES.map(([weak, strong]) => ({
        id: `${weak}-${strong}`,
        source: weak,
        target: strong,
        type: "straight",
        markerEnd: { type: MarkerType.ArrowClosed, color: "var(--line-strong)" },
        style: { stroke: "var(--line-strong)" },
      })),
    [],
  );

  const worldNodes = useMemo<Node[]>(
    () =>
      WORLDS.map((world) => ({
        id: world.id,
        position: { x: world.x, y: world.y },
        data: {
          label: (
            <div className="text-center">
              <span className="eyebrow">{world.id === currentWorld ? "Viewpoint" : "World"}</span>
              <strong className="mt-1 block font-serif text-xl">{world.label}</strong>
              <span className="mt-1 block text-xs text-[var(--muted)]">p = {truthLabel(valuation[world.id])}</span>
            </div>
          ),
        },
        draggable: false,
        selectable: true,
        style: {
          width: 132,
          borderColor: world.id === currentWorld ? "var(--accent)" : "var(--line-strong)",
          borderWidth: world.id === currentWorld ? 2 : 1,
          background: world.id === currentWorld ? "var(--callout)" : "var(--paper)",
          color: "var(--ink)",
          borderRadius: 999,
          padding: 12,
        },
      })),
    [currentWorld, valuation],
  );

  const worldFlowEdges = useMemo<Edge[]>(
    () =>
      witnessEdges.map((edge, index) => ({
        id: `${edge.source}-${edge.target}-${index}`,
        source: edge.source,
        target: edge.target,
        type: edge.source === edge.target ? "smoothstep" : "default",
        markerEnd: { type: MarkerType.ArrowClosed, color: "var(--line-strong)" },
        style: { stroke: "var(--line-strong)" },
      })),
    [witnessEdges],
  );

  const toggleWorldTruth = (world: WorldId) => {
    updateState((current) => ({ valuation: { ...current.valuation, [world]: !current.valuation[world] } }));
  };

  return (
    <div className="mt-10 space-y-12">
      <section className="grid gap-5 lg:grid-cols-[minmax(0,1.55fr)_minmax(18rem,0.7fr)]">
        <div className="min-w-0 overflow-hidden rounded-2xl border border-[var(--line)] bg-[var(--paper)]">
          <div className="border-b border-[var(--line)] px-5 py-4">
            <p className="eyebrow">Bird&apos;s-eye view</p>
            <h2 className="mt-1 font-serif text-3xl tracking-[-0.04em]">The modal cube</h2>
            <p className="mt-2 max-w-2xl text-sm leading-6 text-[var(--muted)]">
              Arrows point from a weaker normal modal logic to an immediate stronger extension. Select a node, or use the system list below, to inspect its frame conditions.
            </p>
          </div>
          <div aria-label="Modal cube graph; the system list below contains the same nodes and extensions" className="h-[34rem] min-h-[28rem] w-full" role="group">
            <ReactFlow
              edges={cubeEdges}
              fitView
              fitViewOptions={{ padding: 0.12 }}
              maxZoom={1.4}
              minZoom={0.35}
              nodes={cubeNodes}
              nodesConnectable={false}
              nodesDraggable={false}
              onNodeClick={(_, node) => setSelectedSystemId(node.id as ModalSystemId)}
              proOptions={{ hideAttribution: true }}
            >
              <Background gap={24} size={1} />
              <Controls showInteractive={false} />
            </ReactFlow>
          </div>
          <fieldset className="border-t border-[var(--line)] px-5 py-4">
            <legend className="sr-only">Modal systems</legend>
            <ul className="grid gap-2 sm:grid-cols-3 lg:grid-cols-5">
              {MODAL_SYSTEMS.map((candidate) => {
                const extensions = MODAL_CUBE_EDGES.filter(([weak]) => weak === candidate.id).map(([, strong]) => strong);
                return (
                  <li key={candidate.id}>
                    <button
                      aria-describedby={`modal-system-${candidate.id}-extensions`}
                      aria-pressed={candidate.id === selectedSystemId}
                      className="min-h-11 w-full rounded-xl border border-[var(--line)] px-3 py-2 text-left text-sm transition hover:border-[var(--line-strong)] aria-pressed:border-[var(--accent)] aria-pressed:bg-[var(--callout)]"
                      onClick={() => setSelectedSystemId(candidate.id)}
                      type="button"
                    >
                      <strong className="font-serif">{candidate.name}</strong>
                      <span className="block text-[11px] text-[var(--muted)]" id={`modal-system-${candidate.id}-extensions`}>
                        {extensions.length ? `extended by ${extensions.join(", ")}` : "strongest system"}
                      </span>
                    </button>
                  </li>
                );
              })}
            </ul>
          </fieldset>
        </div>

        <aside aria-live="polite" className="rounded-2xl border border-[var(--line)] p-5">
          <p className="eyebrow">Selected system</p>
          <h2 className="mt-2 font-serif text-4xl tracking-[-0.05em]">{system.name}</h2>
          <p className="mt-3 text-sm leading-6 text-[var(--muted)]">{system.description}</p>

          <div className="mt-6">
            <h3 className="text-sm font-semibold">Axiom closure</h3>
            <div className="mt-3 flex flex-wrap gap-2">
              {(["D", "T", "B", "4", "5"] as const).map((axiom) => (
                <span
                  className={`rounded-full border px-3 py-1 text-sm ${
                    axioms.has(axiom)
                      ? "border-[var(--accent)] bg-[var(--callout)] text-[var(--ink)]"
                      : "border-[var(--line)] text-[var(--muted)]"
                  }`}
                  key={axiom}
                >
                  {axiom}
                </span>
              ))}
            </div>
          </div>

          <div className="mt-6">
            <h3 className="text-sm font-semibold">Required frame conditions</h3>
            <ul className="mt-3 space-y-2 text-sm text-[var(--muted)]">
              {[...required].map((condition) => (
                <li className="flex items-center justify-between gap-3" key={condition}>
                  <span>{conditionLabels[condition]}</span>
                  <span className="font-mono text-xs text-[var(--ink)]">
                    {Object.values(AXIOMS).find((axiom) => axiom.condition === condition)?.id}
                  </span>
                </li>
              ))}
              {!required.size ? <li>No additional condition beyond K.</li> : null}
            </ul>
          </div>
        </aside>
      </section>

      <section className="grid gap-5 lg:grid-cols-[minmax(0,1.35fr)_minmax(20rem,0.8fr)]">
        <div className="min-w-0 overflow-hidden rounded-2xl border border-[var(--line)] bg-[var(--paper)]">
          <div className="border-b border-[var(--line)] px-5 py-4">
            <p className="eyebrow">Inside one frame</p>
            <h2 className="mt-1 font-serif text-3xl tracking-[-0.04em]">Possible-world perspective</h2>
            <p className="mt-2 text-sm leading-6 text-[var(--muted)]">
              Click a world, or use the viewpoint buttons below, to move the viewpoint. Toggle p to change the valuation without changing accessibility.
            </p>
          </div>
          <div aria-label="Possible-world graph; the accessibility table below lists the same edges" className="h-[24rem] min-h-[20rem] w-full" role="group">
            <ReactFlow
              edges={worldFlowEdges}
              fitView
              fitViewOptions={{ padding: 0.28 }}
              maxZoom={1.6}
              minZoom={0.5}
              nodes={worldNodes}
              nodesConnectable={false}
              nodesDraggable={false}
              onNodeClick={(_, node) => setCurrentWorld(node.id as WorldId)}
              proOptions={{ hideAttribution: true }}
            >
              <Background gap={24} size={1} />
              <Controls showInteractive={false} />
            </ReactFlow>
          </div>
          <fieldset className="flex flex-wrap gap-2 border-t border-[var(--line)] px-5 py-4">
            <legend className="sr-only">Viewpoint world</legend>
            {WORLDS.map((world) => (
              <button
                aria-pressed={world.id === currentWorld}
                className="min-h-11 rounded-full border border-[var(--line)] px-4 text-sm transition hover:border-[var(--line-strong)] aria-pressed:border-[var(--accent)] aria-pressed:bg-[var(--callout)]"
                key={world.id}
                onClick={() => setCurrentWorld(world.id)}
                type="button"
              >
                View from {world.label}
              </button>
            ))}
          </fieldset>
          <fieldset className="flex flex-wrap gap-2 border-t border-[var(--line)] px-5 py-4">
            <legend className="sr-only">Valuation of p</legend>
            {WORLDS.map((world) => (
              <button
                aria-pressed={valuation[world.id]}
                className="min-h-11 rounded-full border border-[var(--line)] px-4 text-sm transition hover:border-[var(--line-strong)]"
                key={world.id}
                onClick={() => toggleWorldTruth(world.id)}
                type="button"
              >
                {world.label}: p {valuation[world.id] ? "✓" : "×"}
              </button>
            ))}
            <button
              className="min-h-11 rounded-full border border-[var(--line)] px-4 text-sm text-[var(--muted)] transition hover:border-[var(--line-strong)]"
              onClick={() => setValuation(DEFAULT_VALUATION)}
              type="button"
            >
              Reset Lean example
            </button>
          </fieldset>
          <div className="overflow-x-auto border-t border-[var(--line)] px-5 py-4">
            <table className="w-full text-left text-sm">
              <caption className="pb-2 text-left text-xs text-[var(--muted)]">Accessibility relation of the displayed witness frame</caption>
              <thead>
                <tr>
                  <th className="py-1 pr-4 font-semibold" scope="col">World</th>
                  <th className="py-1 pr-4 font-semibold" scope="col">p</th>
                  <th className="py-1 font-semibold" scope="col">Accesses</th>
                </tr>
              </thead>
              <tbody>
                {WORLDS.map((world) => {
                  const targets = witnessEdges.filter((edge) => edge.source === world.id).map((edge) => edge.target);
                  return (
                    <tr className="border-t border-[var(--line)]" key={world.id}>
                      <th className="py-1 pr-4 font-normal" scope="row">
                        {world.label}
                        {world.id === currentWorld ? " (viewpoint)" : ""}
                      </th>
                      <td className="py-1 pr-4">{truthLabel(valuation[world.id])}</td>
                      <td className="py-1">{targets.length ? targets.join(", ") : "none"}</td>
                    </tr>
                  );
                })}
              </tbody>
            </table>
          </div>
        </div>

        <div className="space-y-5">
          <section aria-live="polite" className="rounded-2xl border border-[var(--line)] p-5">
            <p className="eyebrow">At {currentWorld}</p>
            <div className="mt-4 grid grid-cols-3 gap-3">
              <ModalTruthCard label="p" value={truth.p} />
              <ModalTruthCard label="◇p" value={truth.possibleP} />
              <ModalTruthCard label="□p" value={truth.necessaryP} />
            </div>
            <p className="mt-4 text-sm leading-6 text-[var(--muted)]">
              Accessible worlds: {truth.accessible.length ? truth.accessible.join(", ") : "none"}. □p is true exactly when p holds in every accessible world; ◇p when it holds in at least one.
            </p>
          </section>

          <section className="rounded-2xl border border-[var(--line)] p-5">
            <p className="eyebrow">This concrete witness</p>
            <h3 className="mt-2 font-serif text-2xl">Detected properties</h3>
            <div className="mt-3 flex flex-wrap gap-2">
              {frameConditions.map((condition) => (
                <span
                  className={`rounded-full border px-3 py-1 text-xs ${
                    detected.has(condition)
                      ? "border-[var(--line-strong)] text-[var(--ink)]"
                      : "border-[var(--line)] text-[var(--muted)]"
                  }`}
                  key={condition}
                >
                  {conditionLabels[condition]}
                </span>
              ))}
            </div>
            <p className="mt-4 text-xs leading-5 text-[var(--muted)]">
              A particular frame may satisfy more conditions than its selected logic requires. The logic constrains admissible frames; it does not uniquely determine one graph.
            </p>
          </section>
        </div>
      </section>

      <section className="rounded-2xl border border-[var(--line)]">
        <div className="border-b border-[var(--line)] px-5 py-4">
          <p className="eyebrow">Lean boundary</p>
          <h2 className="mt-1 font-serif text-3xl tracking-[-0.04em]">What is mechanically verified</h2>
        </div>
        <div className="grid gap-px bg-[var(--line)] sm:grid-cols-2 lg:grid-cols-3">
          {[...axioms].map((axiomId) => {
            const axiom = AXIOMS[axiomId];
            return (
              <article className="bg-[var(--paper)] p-5" key={axiom.id}>
                <div className="flex items-start justify-between gap-3">
                  <strong className="font-serif text-2xl">{axiom.id}</strong>
                  <code className="text-xs text-[var(--muted)]">{axiom.condition}</code>
                </div>
                <p className="mt-2 font-mono text-sm">{axiom.formula}</p>
                <p className="mt-3 text-sm leading-6 text-[var(--muted)]">{axiom.explanation}</p>
                <p className="mt-3 break-all font-mono text-[11px] text-[var(--muted)]">{axiom.leanTheorem}</p>
              </article>
            );
          })}
          {!axioms.size ? (
            <article className="bg-[var(--paper)] p-5 sm:col-span-2 lg:col-span-3">
              <strong>K needs no extra frame condition.</strong>
              <p className="mt-2 text-sm text-[var(--muted)]">Distribution is proved for every Kripke frame by TruthCore.Modal.axiomK_valid.</p>
            </article>
          ) : null}
        </div>
        <aside className="border-t border-[var(--line)] bg-[var(--callout)] px-5 py-4 text-sm leading-6 text-[var(--muted)]">
          The React view evaluates a finite example frame. Lean proves the generic frame-condition ⇒ axiom-validity theorems and the S4 example. It does not turn a chosen modal system into a claim that its metaphysical interpretation is true.
          {selectedSystemId === "S4" ? " The currently displayed S4 witness matches TruthCore.Modal.Examples.frame_is_s4." : ""}
        </aside>
      </section>
    </div>
  );
}

function ModalTruthCard({ label, value }: { label: string; value: boolean }) {
  return (
    <div className="rounded-xl border border-[var(--line)] p-3 text-center">
      <div className="font-serif text-2xl">{label}</div>
      <div className={`mt-1 text-xs font-semibold uppercase tracking-[0.14em] ${value ? "text-[var(--ink)]" : "text-[var(--muted)]"}`}>
        {truthLabel(value)}
      </div>
    </div>
  );
}
