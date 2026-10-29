import { execFileSync } from "node:child_process";
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import { isExpressionNode, type StructureDeclaration } from "./proposition-structure";

export type StrengthObligation = {
  role: string; result_id: string; theorem: string; argument_id: string; bound: true;
  expected_type: string; actual_type: string;
  theorem_application?: string;
  axioms?: string[]; permitted_axioms?: string[];
};
export type StrengthComparison = {
  id: string; stronger_statement_id: string; weaker_statement_id: string; delta_statement_id: string;
  remainder_statement_id?: string; background_statement_ids: string[]; comparison_spec: string; note: string;
  verified: true;
  comparison_status: "strict strengthening" | "proved equivalence" | "proved implication" | "unresolved";
  converse_status: "proved" | "refuted by separating setting" | "unresolved";
  delta_status: "exact factorization proved" | "sufficient only; exactness unresolved" | "unresolved";
  remainder_status?: "exact admitted-only remainder proved" | "unresolved";
  explanatory_status: string;
  explanatory_controls: Array<{ result_id: string; argument_id: string; theorem: string; description: string }>;
  obligations: StrengthObligation[];
  binding: {
    parameters: Array<{ name: string; type: string; binder_info?: string }>;
    formulas: { background: string[]; stronger: string; weaker: string; delta: string; remainder: string };
    specification_application?: string;
    application?: string;
    explicit_application?: string;
    universe_parameters?: string[];
    field_bindings: Array<{ role: string; declaration: string; parameter_indices: number[]; expected_application: string; expression: string; explicit_application?: string; type: string; bound: true }>;
    structure?: StructureDeclaration[];
    references?: Array<{ declaration: string; type?: string; fields?: Array<{ declaration: string; type: string; is_law?: boolean }> }>;
  };
  separator?: { setting: string; result_id: string; theorem: string; bound: true; application?: string; explicit_application?: string; expected_type?: string; actual_type?: string; axioms?: string[]; parameters?: Array<{ expression: string; type: string }> };
  remaining_obligations: string[];
  definitions: Array<{ id: string; term: string; definition: string; note?: string }>;
  disambiguations: Array<{ id: string; term?: string; resolution: string }>;
  provenance: { result_ids: string[]; bind_check: "bound"; semantic_binding: "definitional equality"; comparator: "passed" };
  scope_notes: string[];
};
function record(value: unknown): value is Record<string, unknown> { return typeof value === "object" && value !== null && !Array.isArray(value); }
function strings(value: unknown): value is string[] { return Array.isArray(value) && value.every((item: unknown) => typeof item === "string"); }
function obligation(value: unknown): boolean {
  return record(value) && value.bound === true && ["role", "result_id", "theorem", "argument_id", "expected_type", "actual_type"].every((key) => typeof value[key] === "string");
}
/** Validate the trusted producer's transport; never derive fresh proof status here. */
export function parseStrengthComparisons(value: unknown): StrengthComparison[] {
  if (!record(value) || value.schema_version !== 2 || !record(value.producer) || value.producer.mode !== "live-verified"
    || typeof value.producer.input_digest !== "string" || !Array.isArray(value.comparisons)) throw new Error("Invalid certified comparison bundle");
  for (const entry of value.comparisons) {
    if (!record(entry) || entry.verified !== true
      || !["id", "stronger_statement_id", "weaker_statement_id", "delta_statement_id", "comparison_spec", "note"].every((key) => typeof entry[key] === "string")
      || !strings(entry.background_statement_ids) || !strings(entry.remaining_obligations) || !strings(entry.scope_notes)
      || !["strict strengthening", "proved equivalence", "proved implication", "unresolved"].includes(String(entry.comparison_status))
      || !["proved", "refuted by separating setting", "unresolved"].includes(String(entry.converse_status))
      || !["exact factorization proved", "sufficient only; exactness unresolved", "unresolved"].includes(String(entry.delta_status))
      || typeof entry.explanatory_status !== "string" || !Array.isArray(entry.explanatory_controls)
      || !entry.explanatory_controls.every((item: unknown) => record(item) && ["result_id", "argument_id", "theorem", "description"].every((key) => typeof item[key] === "string"))
      || !Array.isArray(entry.obligations) || !entry.obligations.every(obligation)
      || !record(entry.binding) || !Array.isArray(entry.binding.parameters) || !entry.binding.parameters.every((parameter: unknown) => record(parameter) && typeof parameter.name === "string" && typeof parameter.type === "string")
      || !record(entry.binding.formulas) || !strings(entry.binding.formulas.background)
      || !["stronger", "weaker", "delta", "remainder"].every((key) => record(entry.binding) && record(entry.binding.formulas) && typeof entry.binding.formulas[key] === "string")
      || !Array.isArray(entry.definitions) || !entry.definitions.every((item: unknown) => record(item) && ["id", "term", "definition"].every((key) => typeof item[key] === "string"))
      || !Array.isArray(entry.disambiguations) || !entry.disambiguations.every((item: unknown) => record(item) && typeof item.id === "string" && typeof item.resolution === "string")
      || !record(entry.provenance) || !strings(entry.provenance.result_ids) || entry.provenance.bind_check !== "bound"
      || entry.provenance.semantic_binding !== "definitional equality" || entry.provenance.comparator !== "passed") throw new Error("Invalid certified comparison");
    if (entry.binding.structure !== undefined && (!Array.isArray(entry.binding.structure) || !entry.binding.structure.every((item: unknown) => record(item) && typeof item.declaration === "string"
      && (item.type === undefined || isExpressionNode(item.type)) && (item.expansion === undefined || isExpressionNode(item.expansion))))) throw new Error("Invalid comparison expression structure");
    const expectedFields = ["stronger", "weaker", "delta", ...entry.background_statement_ids.map((_, i) => `background.${i}`), ...(entry.remainder_statement_id ? ["remainder"] : [])];
    const fields = entry.binding.field_bindings;
    if (!Array.isArray(fields) || fields.length !== expectedFields.length
      || new Set(fields.map((f: unknown) => record(f) ? f.role : undefined)).size !== fields.length
      || !fields.every((f: unknown) => record(f) && f.bound === true && expectedFields.includes(String(f.role))
        && typeof f.declaration === "string" && typeof f.expected_application === "string" && typeof f.explicit_application === "string"
        && Array.isArray(f.parameter_indices) && f.parameter_indices.every((n: unknown, i: number, ns: unknown[]) => typeof n === "number" && Number.isInteger(n) && n >= 0 && (i === 0 || n > (ns[i - 1] as number))))) throw new Error("Invalid complete statement application binding");
    const roles = new Set(entry.obligations.map((item) => (item as StrengthObligation).role));
    const separated = record(entry.separator) && entry.separator.bound === true && ["setting", "result_id", "theorem"].every((key) => record(entry.separator) && typeof entry.separator[key] === "string");
    if ((entry.separator !== undefined && !separated)
      || (entry.remainder_status !== undefined && !["exact admitted-only remainder proved", "unresolved"].includes(String(entry.remainder_status)))
      || (entry.remainder_status === "exact admitted-only remainder proved" && !["allowed_cases", "remainder_identity"].every((role) => roles.has(role)))
      || (entry.comparison_status === "strict strengthening" && (!separated || !roles.has("implication")))
      || (entry.comparison_status === "proved equivalence" && (!roles.has("implication") || !roles.has("converse")))
      || (entry.converse_status === "refuted by separating setting" && !separated)
      || (entry.converse_status === "proved" && !roles.has("converse"))
      || (entry.delta_status === "exact factorization proved" && !["implication", "delta_forward", "reconstruction", "equivalence"].every((role) => roles.has(role)))) throw new Error("Comparison label lacks its certified evidence");
  }
  return value.comparisons as StrengthComparison[];
}
let cached: StrengthComparison[] | undefined;
/** Static presentation input. Source freshness is owned by the existing Python producer. */
export function getStrengthComparisons(): StrengthComparison[] {
  if (cached === undefined) {
    const root = path.resolve(process.cwd(), "../..");
    const artifact = path.resolve(root, process.env.TRUTH_CORE_STRENGTH_REPORT ?? ".cache/strength-comparisons.json");
    if (artifact !== path.join(root, ".cache/strength-comparisons.json")) throw new Error("Strength report must use .cache/strength-comparisons.json");
    if (!existsSync(artifact)) {
      if (process.env.TRUTH_CORE_REQUIRE_STRENGTH_REPORT === "true") throw new Error("Certified comparison input missing; run bun run strength-inputs");
      cached = [];
    } else {
      execFileSync("python3", ["scripts/corpus.py", "strength-report", "--check-input", "--output", artifact], { cwd: root, timeout: 60000, stdio: "pipe" });
      cached = parseStrengthComparisons(JSON.parse(readFileSync(artifact, "utf8")));
    }
  }
  return cached;
}
export function comparisonsForStatement(comparisons: StrengthComparison[], id: string): StrengthComparison[] {
  return comparisons.filter((entry) => [entry.stronger_statement_id, entry.weaker_statement_id, entry.delta_statement_id, entry.remainder_statement_id, ...entry.background_statement_ids].includes(id));
}
export function comparisonsForResult(comparisons: StrengthComparison[], id: string): StrengthComparison[] {
  return comparisons.filter((entry) => entry.provenance.result_ids.includes(id) || entry.explanatory_controls.some((control) => control.result_id === id));
}
