import { execFileSync } from "node:child_process";
import path from "node:path";

import type { CorpusStatement } from "./corpus";
import type { ClosureReason } from "./site-state";

const attemptKinds = ["derivation", "refutation", "reading", "countermodel", "source-search"] as const;
const attemptOutcomes = ["succeeded", "failed", "blocked", "superseded"] as const;

export type CorpusAttempt = {
  id: string;
  statement_ids: string[];
  date: string;
  kind: (typeof attemptKinds)[number];
  summary: string;
  evidence: string[];
} & ({ outcome: "blocked"; blocker: string } | { outcome: Exclude<(typeof attemptOutcomes)[number], "blocked">; blocker?: string });

export type PremiseDossier = {
  statement: Pick<CorpusStatement, "id" | "paraphrase" | "lean_declaration">;
  root: string;
  closure: ClosureReason | null;
  established: boolean;
  frontier: { depth: "bare" | "sourced"; path_to_root: string[] | null } | null;
  claim_ids: string[];
  supporting_claim_ids: string[];
  definition_ids: string[];
  disambiguation_ids: string[];
  argument_ids: string[];
  result_ids: string[];
  transcription_result_ids: string[];
  instantiation_result_ids: string[];
  alternative_relation_ids: string[];
  objection_relation_ids: string[];
  countermodel_attempt_ids: string[];
  attempts: CorpusAttempt[];
  route_contributions: Array<{ argument_id: string; cost: number; open_leaf: boolean; direct_premise: boolean }>;
};

function record(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}
function strings(value: unknown): value is string[] {
  return Array.isArray(value) && value.every((item) => typeof item === "string");
}
function oneOf<const T extends readonly string[]>(values: T, value: unknown): value is T[number] {
  return typeof value === "string" && values.some((entry) => entry === value);
}
function attempt(value: unknown): value is CorpusAttempt {
  return record(value) && typeof value.id === "string" && strings(value.statement_ids)
    && typeof value.date === "string" && oneOf(attemptKinds, value.kind) && oneOf(attemptOutcomes, value.outcome)
    && typeof value.summary === "string" && strings(value.evidence)
    && (value.blocker === undefined || typeof value.blocker === "string")
    && (value.outcome !== "blocked" || typeof value.blocker === "string");
}
function dossier(value: unknown): value is PremiseDossier {
  if (!record(value) || !record(value.statement) || typeof value.statement.id !== "string"
    || typeof value.statement.paraphrase !== "string"
    || (value.statement.lean_declaration !== undefined && typeof value.statement.lean_declaration !== "string")
    || typeof value.root !== "string" || (value.closure !== null && !oneOf(["proved", "self_evident", "alternatives_refuted", "via_transcription"], value.closure))
    || typeof value.established !== "boolean") {
    return false;
  }
  if (value.frontier !== null && (!record(value.frontier) || !oneOf(["bare", "sourced"], value.frontier.depth)
    || (value.frontier.path_to_root !== null && !strings(value.frontier.path_to_root)))) {
    return false;
  }
  const idLists = ["claim_ids", "supporting_claim_ids", "definition_ids", "disambiguation_ids", "argument_ids", "result_ids",
    "transcription_result_ids", "instantiation_result_ids", "alternative_relation_ids", "objection_relation_ids", "countermodel_attempt_ids"];
  return idLists.every((key) => strings(value[key])) && Array.isArray(value.attempts) && value.attempts.every(attempt)
    && Array.isArray(value.route_contributions) && value.route_contributions.every((route: unknown) => record(route)
      && typeof route.argument_id === "string" && typeof route.cost === "number" && Number.isInteger(route.cost) && route.cost >= 0
      && typeof route.open_leaf === "boolean" && typeof route.direct_premise === "boolean");
}

/** Python validates references; this boundary validates the generated transport shape. */
export function parseDossiers(value: unknown): Record<string, PremiseDossier> {
  if (!record(value)) {
    throw new Error("Dossier report must be an object");
  }
  const result: Record<string, PremiseDossier> = {};
  for (const [id, entry] of Object.entries(value)) {
    if (!dossier(entry) || entry.statement.id !== id) {
      throw new Error(`Invalid dossier report for ${id}`);
    }
    result[id] = entry;
  }
  return result;
}

let cached: Record<string, PremiseDossier> | undefined;

/** Build once for all static pages; closure and route costs stay owned by corpus.py. */
export function getDossiers(): Record<string, PremiseDossier> {
  if (!cached) {
    const output: unknown = JSON.parse(execFileSync("python3", ["scripts/corpus.py", "dossier", "--all", "--json"], {
      cwd: path.resolve(process.cwd(), "../.."), encoding: "utf8", maxBuffer: 64 * 1024 * 1024,
    }));
    cached = parseDossiers(output);
  }
  return cached;
}
