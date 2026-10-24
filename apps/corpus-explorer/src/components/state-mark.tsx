import { CLOSURE_LABELS, type ResultKind, type StatementState } from "@/lib/site-state";

type Tone = "proved" | "conditional" | "self-evident" | "defended" | "transcription" | "open" | "source-only" | "objection";

function Mark({ tone, children, title }: { tone: Tone; children: React.ReactNode; title?: string }) {
  return (
    <span className="state-mark" data-tone={tone} title={title}>
      <span aria-hidden="true" className="state-mark-dot" />
      {children}
    </span>
  );
}

/** Frontier status of a statement, as `corpus.py frontier` reports it. */
export function StatementStateMark({ state }: { state: StatementState }) {
  if (state.kind === "closed") {
    const tone: Tone =
      state.reason === "proved"
        ? "proved"
        : state.reason === "self_evident"
          ? "self-evident"
          : state.reason === "alternatives_refuted"
            ? "defended"
            : "transcription";
    return state.established ? (
      <Mark tone={tone} title="Established: it rests only on self-evident or defended statements, through verified results">
        {CLOSURE_LABELS[state.reason]} · established
      </Mark>
    ) : (
      <Mark tone="conditional" title="Closed as a node, but some argument beneath it still rests on open premises">
        {CLOSURE_LABELS[state.reason]} · on open premises
      </Mark>
    );
  }
  if (state.kind === "open") {
    return (
      <Mark tone="open" title={state.item.depth === "bare" ? "No claim states it and no source supports it" : "Stated or supported by a source, not yet defended"}>
        Open · {state.item.depth === "bare" ? "bare" : "sourced"}
        {state.item.transcription_only ? " · transcribed only" : ""}
      </Mark>
    );
  }
  return <Mark tone="source-only">Not a premise</Mark>;
}

export function ResultKindMark({ kind }: { kind: ResultKind }) {
  return kind.kind === "transcription" ? (
    <Mark tone="transcription" title="The proof applies one premise that already contains the conclusion (invariant 16)">
      Transcription
    </Mark>
  ) : (
    <Mark tone="proved">Verified derivation</Mark>
  );
}

export function DepthMark({ depth }: { depth: "bare" | "sourced" }) {
  return <Mark tone={depth === "bare" ? "objection" : "open"}>{depth}</Mark>;
}
