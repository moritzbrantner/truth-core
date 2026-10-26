import { execFileSync } from "node:child_process";
import path from "node:path";

import type { Corpus } from "./corpus";
import { DEFAULT_ROOT_STATEMENT_ID } from "./proposition-graph";

/**
 * The project's current state, as computed by `python3 scripts/corpus.py
 * frontier --json` at build time (#200). The explorer does not re-implement
 * the closure rules here: every "closed", "open", "bare" or "sourced" on the
 * state, statement and result pages comes from that report.
 */

export type FrontierDepth = "bare" | "sourced";

export type FrontierItem = {
  statement_id: string;
  paraphrase: string;
  transcription_only: boolean;
  dependent_arguments: string[];
  transitive_dependent_arguments: string[];
  transitive_dependent_statements: string[];
  path_to_root: string[] | null;
  alternatives: Array<{ statement_id: string; refuted: boolean }>;
  objections: string[];
  supporting_claims: string[];
  stating_claims: string[];
  depth: FrontierDepth;
  transcription_premise_of: string[];
};

export type TranscriptionFlag = {
  result_id: string;
  argument_id: string;
  proof_steps: number;
  single_application_of: string | null;
  /** Hypotheses the proof only assembles into a tuple or conjunction (#391). */
  assembly_of?: string[] | null;
  /** Opaque-atom heuristic (#391): a warning only, never a closure rule. */
  opaque_atoms?: boolean;
  goal_consequent_premises: Array<{ hypothesis: string; statement_ids: string[] }>;
};

export type TranscriptionKind = "opaque_atoms" | "single_application" | "assembly" | "instantiation";

/** A transcription result (invariant 16): declared in its record, or found by the heuristics. */
export type TranscriptionResult = { kind: TranscriptionKind; declared: boolean };

export type Refutation = {
  relation_id: string;
  argument_id: string;
  statement_id: string;
  verified: boolean;
  open_premise_statement_ids: string[];
  /** Counts for rule (c) only when verified and every premise is closed (#391). */
  counted: boolean;
};

export type RootRoute = {
  argument_id: string;
  /** Distinct open leaves: sourced or bare premises kept as leaves, intermediate conclusions expanded (#391). */
  cost: number;
  premise_count: number;
  verified: boolean;
  transcription: boolean;
  designated: boolean;
  cheapest: boolean;
  open_premise_statement_ids: string[];
  proved_unestablished_statement_ids: string[];
};

export type ClosureReason = "proved" | "self_evident" | "alternatives_refuted" | "via_transcription";

export type FrontierReport = {
  root: string;
  root_known: boolean;
  transcription_flags: TranscriptionFlag[];
  /** Every result that closes nothing by itself (rule (a) skips it), by ID. */
  transcription_results: Record<string, TranscriptionResult>;
  refutations: Refutation[];
  /** Alternatives refuted by a counted refutation. */
  refuted_statements: string[];
  routes: { root: string | null; cheapest_argument_id: string | null; routes: RootRoute[] };
  closed_via_transcription: Array<{
    statement_id: string;
    result_id: string;
    argument_id: string;
    premise_statement_ids: string[];
    path_to_root: string[] | null;
  }>;
  closed_statements: Record<string, ClosureReason>;
  /** Self-evident or defended, or reached from such statements through verified results only. */
  established_statements: string[];
  alternatives_recorded: boolean;
  open_premise_count: number;
  depth_counts: Record<FrontierDepth, number>;
  items: FrontierItem[];
};

const repositoryRoot = path.resolve(process.cwd(), "../..");
let cachedReport: FrontierReport | null = null;

export function getFrontierReport(): FrontierReport {
  if (!cachedReport) {
    cachedReport = JSON.parse(
      execFileSync("python3", ["scripts/corpus.py", "frontier", "--json"], {
        cwd: repositoryRoot,
        encoding: "utf8",
        maxBuffer: 64 * 1024 * 1024,
      }),
    ) as FrontierReport;
  }
  return cachedReport;
}

export type BuildInfo = {
  commit: string;
  shortCommit: string;
  commitTime: string;
  builtAt: string;
  repositoryUrl: string;
};

const REPOSITORY_URL = "https://github.com/moritzbrantner/truth-core";
let cachedBuild: BuildInfo | null = null;

function git(...args: string[]) {
  try {
    return execFileSync("git", args, { cwd: repositoryRoot, encoding: "utf8" }).trim();
  } catch {
    return "";
  }
}

export function getBuildInfo(): BuildInfo {
  if (!cachedBuild) {
    const commit = process.env.GITHUB_SHA || git("rev-parse", "HEAD") || "unknown";
    cachedBuild = {
      commit,
      shortCommit: commit.slice(0, 7),
      commitTime: git("log", "-1", "--format=%cI", commit) || "",
      builtAt: new Date().toISOString(),
      repositoryUrl: REPOSITORY_URL,
    };
  }
  return cachedBuild;
}

export function formatUtc(iso: string) {
  return `${new Date(iso).toISOString().slice(0, 16).replace("T", " ")} UTC`;
}

/** GitHub link to a repository file at the built commit. */
export function sourceUrl(file: string, line?: number) {
  const build = getBuildInfo();
  return `${build.repositoryUrl}/blob/${build.commit}/${file}${line ? `#L${line}` : ""}`;
}

export type StatementState =
  | { kind: "closed"; reason: ClosureReason; established: boolean }
  | { kind: "open"; item: FrontierItem }
  | { kind: "unused" };

export function statementState(report: FrontierReport, statementId: string): StatementState {
  const reason = report.closed_statements[statementId];
  if (reason) return { kind: "closed", reason, established: report.established_statements.includes(statementId) };
  const item = report.items.find((entry) => entry.statement_id === statementId);
  return item ? { kind: "open", item } : { kind: "unused" };
}

/**
 * A result is a transcription (invariant 16) when `corpus.py frontier` lists it
 * in `transcription_results`: its record declares a `transcription` kind, or
 * its proof is a single application of one hypothesis or only assembles
 * hypotheses (#391). That set is what closure uses. The other flags (goal as a
 * premise consequent, a short proof, opaque atoms without a declaration) are
 * heuristic warnings only.
 */
export type ResultKind = {
  kind: "derivation" | "transcription";
  flag?: TranscriptionFlag;
  transcription?: TranscriptionResult;
};

export function resultKind(report: FrontierReport, resultId: string): ResultKind {
  const flag = report.transcription_flags.find((entry) => entry.result_id === resultId);
  const transcription = report.transcription_results[resultId];
  return { kind: transcription ? "transcription" : "derivation", flag, transcription };
}

export const TRANSCRIPTION_KIND_DESCRIPTIONS: Record<TranscriptionKind, string> = {
  opaque_atoms: "Every proposition the theorem relates is an unconstrained Prop parameter.",
  single_application: "The proof applies one premise whose consequent is the conclusion.",
  assembly: "The proof only pairs or destructures its hypotheses.",
  instantiation: "The proof only instantiates a general premise or lemma at the case.",
};

export const CLOSURE_LABELS: Record<ClosureReason, string> = {
  proved: "Proved",
  self_evident: "Self-evident",
  alternatives_refuted: "Alternatives refuted",
  via_transcription: "Closed through closed premises",
};

export const CLOSURE_DESCRIPTIONS: Record<ClosureReason, string> = {
  proved: "Conclusion of a verified result that is not a transcription.",
  self_evident: "Marked self-evident, with a sourced justification.",
  alternatives_refuted: "Every recorded alternative is refuted by a verified argument whose premises are all closed.",
  via_transcription: "Conclusion of a transcription result whose premises are all closed.",
};

export type Rival = {
  relationId: string;
  subject: string;
  subjectKind: string;
  target: string;
  refutedBy: string[];
};

/**
 * Recorded alternatives (with the refutations that count: a verified argument
 * whose premises are all closed, #391) and objections.
 */
export function rivals(corpus: Corpus, report: FrontierReport) {
  const refuters = new Map<string, string[]>();
  for (const refutation of report.refutations) {
    if (refutation.counted) {
      refuters.set(refutation.statement_id, [...(refuters.get(refutation.statement_id) ?? []), refutation.argument_id]);
    }
  }
  const of = (predicate: string): Rival[] =>
    corpus.relations
      .filter((relation) => relation.predicate === predicate)
      .map((relation) => ({
        relationId: relation.id,
        subject: relation.subject_id,
        subjectKind: relation.subject_kind,
        target: relation.object_id,
        refutedBy: refuters.get(relation.subject_id) ?? [],
      }))
      .sort((a, b) => a.target.localeCompare(b.target) || a.subject.localeCompare(b.subject));
  return { alternatives: of("alternative_to"), objections: of("attacks") };
}

export { DEFAULT_ROOT_STATEMENT_ID };
