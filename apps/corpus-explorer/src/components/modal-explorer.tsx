"use client";

import { Background, Controls, MarkerType, ReactFlow, type Edge, type Node } from "@xyflow/react";
import { useMemo, useState } from "react";

import {
  AXIOMS,
  MODAL_CUBE_EDGES,
  MODAL_SYSTEMS,
  WORLDS,
  buildWitnessFrame,
  detectFrameConditions,
  impliedAxioms,
  modalTruthAt,
  requiredConditions,
  type ModalSystemId,
  type WorldId,
} from "@/lib/modal-cube";

const defaultValuation: Record<WorldId, boolean> = {
  actual: false,
  nearby: false,
  remote: true,
};

const conditionLabels = {
  serial: "serial",
  reflexive: "reflexive",
  symmetric: "symmetric",
  transitive: "transitive",
  euclidean: "Euclidean",
} as const;

function truthLabel(value: boolean) {
  return value ? "true" : "false";
}

export function ModalExplorer() {
  const [selectedSystemId, setSelectedSystemId] = useState<ModalSystemId>("S4");
  const [currentWorld, setCurrentWorld] = useState<WorldId>("actual");
  const [valuation, setValuation] = useState<Record<WorldId, boolean>>(defaultValuation);

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
    setValuation((current) => ({ ...current, [world]: !current[world] }));
  };

  return (
    <div className="mt-10 space-y-12">
      <section className="grid gap-5 lg:grid-cols-[minmax(0,1.55fr)_minmax(18rem,0.7fr)]">
        <div className="min-w-0 overflow-hidden rounded-2xl border border-[var(--line)] bg-[var(--panel)]">
          <div className="border-b border-[var(--line)] px-5 py-4">
            <p className="eyebrow">Bird&apos;s-eye view</p>
            <h2 className="mt-1 font-serif text-3xl tracking-[-0.04em]">The modal cube</h2>
            <p className="mt-2 max-w-2xl text-sm leading-6 text-[var(--muted)]">
              Arrows point from a weaker normal modal logic to an immediate stronger extension. Select a node to inspect its frame conditions.
            </p>
          </div>
          <div className="h-[34rem] min-h-[28rem] w-full">
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
        </div>

        <aside className="rounded-2xl border border-[var(--line)] p-5">
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
        <div className="min-w-0 overflow-hidden rounded-2xl border border-[var(--line)] bg-[var(--panel)]">
          <div className="border-b border-[var(--line)] px-5 py-4">
            <p className="eyebrow">Inside one frame</p>
            <h2 className="mt-1 font-serif text-3xl tracking-[-0.04em]">Possible-world perspective</h2>
            <p className="mt-2 text-sm leading-6 text-[var(--muted)]">
              Click a world to move the viewpoint. Toggle p below to change the valuation without changing accessibility.
            </p>
          </div>
          <div className="h-[24rem] min-h-[20rem] w-full">
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
          <div className="flex flex-wrap gap-2 border-t border-[var(--line)] px-5 py-4">
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
              onClick={() => setValuation(defaultValuation)}
              type="button"
            >
              Reset Lean example
            </button>
          </div>
        </div>

        <div className="space-y-5">
          <section className="rounded-2xl border border-[var(--line)] p-5">
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
              {["serial", "reflexive", "symmetric", "transitive", "euclidean"].map((condition) => (
                <span
                  className={`rounded-full border px-3 py-1 text-xs ${
                    detected.has(condition as keyof typeof conditionLabels)
                      ? "border-[var(--line-strong)] text-[var(--ink)]"
                      : "border-[var(--line)] text-[var(--muted)]"
                  }`}
                  key={condition}
                >
                  {condition === "euclidean" ? "Euclidean" : condition}
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
