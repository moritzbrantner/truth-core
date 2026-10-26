import { execFileSync } from "node:child_process";
import path from "node:path";

type Core = { statement_ids: string[]; result_id: string; theorem: string; minimality: string };
export type RegisteredConfigurationCase = {
  id: string;
  seed_statement_id: string;
  semantics: { id: string; logic: string; frame: string; domain: string; identity: string; vocabulary: string };
  configurations: Array<{ id: string; statement_ids: string[]; status: "verification required"; incompatible_cores: Core[]; model_ids: string[] }>;
  inapplicable_models: Array<{ model_id: string; profile_mismatches: Array<{ parameter: string; expected: string; registered: string }> }>;
  verified: false;
  scope: string;
};

function record(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}
function strings(value: unknown): value is string[] {
  return Array.isArray(value) && value.every((item: unknown) => typeof item === "string");
}
function core(value: unknown): value is Core {
  return record(value) && strings(value.statement_ids) && typeof value.result_id === "string"
    && typeof value.theorem === "string" && typeof value.minimality === "string";
}
function semantics(value: unknown): value is RegisteredConfigurationCase["semantics"] {
  return record(value) && ["id", "logic", "frame", "domain", "identity", "vocabulary"].every((key) => typeof value[key] === "string");
}
function configurationCase(value: unknown): value is RegisteredConfigurationCase {
  return record(value) && typeof value.id === "string" && typeof value.seed_statement_id === "string"
    && value.verified === false && typeof value.scope === "string" && semantics(value.semantics)
    && Array.isArray(value.inapplicable_models) && value.inapplicable_models.every((model: unknown) => record(model)
      && typeof model.model_id === "string" && Array.isArray(model.profile_mismatches)
      && model.profile_mismatches.every((item: unknown) => record(item) && typeof item.parameter === "string"
        && typeof item.expected === "string" && typeof item.registered === "string"))
    && Array.isArray(value.configurations) && value.configurations.every((item: unknown) => record(item)
      && typeof item.id === "string" && strings(item.statement_ids) && item.status === "verification required"
      && Array.isArray(item.incompatible_cores) && item.incompatible_cores.every(core) && strings(item.model_ids));
}

export function parseRegisteredConfigurationCases(value: unknown): RegisteredConfigurationCase[] {
  if (!Array.isArray(value) || !value.every(configurationCase)) {
    throw new Error("Invalid registered configuration projection");
  }
  return value;
}

let cached: RegisteredConfigurationCase[] | undefined;

/** Registered provenance only. A static build must never infer fresh verification. */
export function getRegisteredConfigurationCases(): RegisteredConfigurationCase[] {
  if (!cached) {
    const output: unknown = JSON.parse(execFileSync("python3", ["scripts/corpus.py", "configurations", "--registered", "--json"], {
      cwd: path.resolve(process.cwd(), "../.."), encoding: "utf8", timeout: 60000, maxBuffer: 16 * 1024 * 1024,
    }));
    cached = parseRegisteredConfigurationCases(output);
  }
  return cached;
}
