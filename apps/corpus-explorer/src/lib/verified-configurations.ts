import { execFileSync } from "node:child_process";
import path from "node:path";

import type { RegisteredConfigurationCase } from "./configuration-cases";

export type ConfigurationCore = {
  statement_ids: string[];
  result_id: string;
  theorem: string;
  result_ids: string[];
  theorems: string[];
  minimality: string;
  removal_evidence: Array<{ removed_statement_id: string; model_ids: string[] }>;
};
export type CertifiedSelection = {
  id: string;
  statement_ids: string[];
  status: "verified incompatible" | "model witnessed" | "unresolved";
  incompatible_cores: ConfigurationCore[];
  model_ids: string[];
  model_witnesses: Array<{ model_id: string; lean_declaration: string; evaluations: Array<{ statement_id: string; theorem: string; arguments: string[]; value: "satisfies" | "violates" }> }>;
  unresolved_reason: string | null;
  core_composition: { combinations_checked: number; limit: number; truncated: boolean };
};
export type AssumptionNode =
  | { id: string; kind: "decision"; statement_id: string; exclude: string; include: string }
  | { id: string; kind: "terminal"; required_statement_ids: string[]; optional_statement_ids: string[]; report: CertifiedSelection; syntactic_selections_covered: number };
export type VerifiedConfigurationCase = Omit<RegisteredConfigurationCase, "verified" | "configurations"> & {
  verified: true;
  verification: { result_ids: string[]; original_bound_result_ids: string[]; models: { models: number; certificates: number; axioms: string[] }; compositions: { cores: number } };
  family_verification: { cores: number };
  configurations: CertifiedSelection[];
  assumption_space: {
    statement_ids: string[];
    max_dimensions: 10;
    root: string;
    nodes: AssumptionNode[];
    limits: { classifier_calls: number; decision_nodes: number; terminal_families: number; syntactic_selections: number; covered_selections: number; note: string };
  };
  verified_implications: Array<{ result_id: string; theorem: string; premise_statement_ids: string[]; conclusion_statement_id: string }>;
};
export type VerifiedConfigurationBundle = {
  schema_version: 1;
  producer: { mode: "live-verified"; source_head: string; input_digest: string; trust: string };
  cases: VerifiedConfigurationCase[];
};

function record(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}
function strings(value: unknown): value is string[] {
  return Array.isArray(value) && value.every((entry: unknown) => typeof entry === "string");
}
function count(value: unknown): value is number {
  return typeof value === "number" && Number.isSafeInteger(value) && value >= 0;
}
function core(value: unknown): value is ConfigurationCore {
  return record(value) && strings(value.statement_ids) && typeof value.result_id === "string" && typeof value.theorem === "string"
    && strings(value.result_ids) && strings(value.theorems) && value.result_ids.length === value.theorems.length && typeof value.minimality === "string"
    && Array.isArray(value.removal_evidence) && value.removal_evidence.every((item: unknown) => record(item)
      && typeof item.removed_statement_id === "string" && strings(item.model_ids));
}
function selection(value: unknown): value is CertifiedSelection {
  return record(value) && typeof value.id === "string" && strings(value.statement_ids)
    && typeof value.status === "string" && ["verified incompatible", "model witnessed", "unresolved"].includes(value.status)
    && strings(value.model_ids) && Array.isArray(value.incompatible_cores) && value.incompatible_cores.every(core)
    && (value.unresolved_reason === null || typeof value.unresolved_reason === "string")
    && record(value.core_composition) && count(value.core_composition.combinations_checked)
    && count(value.core_composition.limit) && typeof value.core_composition.truncated === "boolean"
    && Array.isArray(value.model_witnesses) && value.model_witnesses.every((model: unknown) => record(model)
      && typeof model.model_id === "string" && typeof model.lean_declaration === "string"
      && Array.isArray(model.evaluations) && model.evaluations.every((entry: unknown) => record(entry)
        && typeof entry.statement_id === "string" && typeof entry.theorem === "string" && strings(entry.arguments)
        && (entry.value === "satisfies" || entry.value === "violates")));
}
function node(value: unknown): value is AssumptionNode {
  if (!record(value) || typeof value.id !== "string") { return false; }
  if (value.kind === "decision") {
    return typeof value.statement_id === "string" && typeof value.exclude === "string" && typeof value.include === "string";
  }
  return value.kind === "terminal" && strings(value.required_statement_ids) && strings(value.optional_statement_ids)
    && count(value.syntactic_selections_covered) && selection(value.report);
}
function verifiedCase(value: unknown): value is VerifiedConfigurationCase {
  if (!record(value) || value.verified !== true || typeof value.id !== "string" || typeof value.seed_statement_id !== "string"
    || typeof value.scope !== "string" || !record(value.semantics)
    || !["id", "logic", "frame", "domain", "identity", "vocabulary"].every((key) => record(value.semantics) && typeof value.semantics[key] === "string")
    || !Array.isArray(value.configurations) || !value.configurations.every(selection)
    || !record(value.verification) || !strings(value.verification.result_ids) || !strings(value.verification.original_bound_result_ids)
    || !record(value.verification.models) || !count(value.verification.models.models) || !count(value.verification.models.certificates) || !strings(value.verification.models.axioms)
    || !record(value.verification.compositions) || !count(value.verification.compositions.cores)
    || !record(value.family_verification) || !count(value.family_verification.cores)
    || !Array.isArray(value.inapplicable_models) || !value.inapplicable_models.every((model: unknown) => record(model)
      && typeof model.model_id === "string" && Array.isArray(model.profile_mismatches)
      && model.profile_mismatches.every((entry: unknown) => record(entry) && typeof entry.parameter === "string" && typeof entry.expected === "string" && typeof entry.registered === "string"))
    || !record(value.assumption_space)) { return false; }
  const space = value.assumption_space;
  if (!strings(space.statement_ids) || space.statement_ids.length > 10 || new Set(space.statement_ids).size !== space.statement_ids.length
    || space.max_dimensions !== 10 || typeof space.root !== "string" || !Array.isArray(space.nodes) || !space.nodes.every(node)
    || !record(space.limits) || typeof space.limits.note !== "string"
    || !["classifier_calls", "decision_nodes", "terminal_families", "syntactic_selections", "covered_selections"].every((key) => record(space.limits) && count(space.limits[key]))) { return false; }
  const nodes = new Map(space.nodes.map((entry) => [entry.id, entry]));
  if (nodes.size !== space.nodes.length || !nodes.has(space.root)) { return false; }
  for (const entry of space.nodes) {
    if (entry.kind === "decision" && (!space.statement_ids.includes(entry.statement_id) || !nodes.has(entry.exclude) || !nodes.has(entry.include))) { return false; }
  }
  return Array.isArray(value.verified_implications) && value.verified_implications.every((entry: unknown) => record(entry)
    && typeof entry.result_id === "string" && typeof entry.theorem === "string" && strings(entry.premise_statement_ids) && typeof entry.conclusion_statement_id === "string");
}

/** Python validates current-input provenance and canonical trees; this validates transport shape. */
export function parseVerifiedConfigurations(value: unknown): VerifiedConfigurationBundle {
  if (!record(value) || value.schema_version !== 1 || !record(value.producer) || value.producer.mode !== "live-verified"
    || typeof value.producer.source_head !== "string" || typeof value.producer.input_digest !== "string" || typeof value.producer.trust !== "string"
    || !Array.isArray(value.cases) || !value.cases.every(verifiedCase)) {
    throw new Error("Invalid verified configuration transport");
  }
  return { schema_version: 1, producer: { mode: "live-verified", source_head: value.producer.source_head,
    input_digest: value.producer.input_digest, trust: value.producer.trust }, cases: value.cases };
}

let cached: VerifiedConfigurationBundle | null | undefined;

/** Only an explicit trusted producer path enables certified rendering. No stale fallback. */
export function getVerifiedConfigurations(): VerifiedConfigurationBundle | null {
  if (cached === undefined) {
    const artifact = process.env.TRUTH_CORE_CONFIGURATION_REPORT;
    if (!artifact) {
      if (process.env.TRUTH_CORE_REQUIRE_CONFIGURATION_REPORT === "true") {
        throw new Error("Certified build requires TRUTH_CORE_CONFIGURATION_REPORT");
      }
      cached = null;
    } else {
      const root = path.resolve(process.cwd(), "../..");
      if (path.resolve(root, artifact) !== path.join(root, ".cache/configuration-explorer.json")) {
        throw new Error("Certified transport must use .cache/configuration-explorer.json for cache invalidation");
      }
      const output: unknown = JSON.parse(execFileSync("python3", ["scripts/corpus.py", "configuration-report", "--check", path.resolve(root, artifact), "--json"], {
        cwd: root, encoding: "utf8", timeout: 60000, maxBuffer: 32 * 1024 * 1024,
      }));
      cached = parseVerifiedConfigurations(output);
    }
  }
  return cached;
}
