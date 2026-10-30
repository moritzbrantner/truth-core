import { execFileSync } from "node:child_process";
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";

export type ExpressionNode = {
  id: string; kind: string; text: string; type: string; coverage: string;
  children: Array<{ role: string; node: ExpressionNode }>;
  declaration?: string; binding?: string; binder_name?: string; binder_info?: string;
  boundary?: string; unfold_available?: boolean;
};
export type StructureDeclaration = {
  declaration: string; type?: ExpressionNode; expansion?: ExpressionNode; error?: string;
  coverage?: string; unfold_status?: string;
  references?: Array<{ declaration: string; type?: string; kind: string; fields?: Array<{ declaration: string; type: string; is_law?: boolean }> }>;
};
type SemanticRecord = { id: string; term?: string; definition?: string; resolution?: string; note?: string; expression_ids?: string[] };
export type StructureReport = {
  statement_id: string; lean_declaration: string;
  revision: { head: string; input_digest: string; inputs: Array<{ path: string; sha256: string }> };
  declarations: StructureDeclaration[];
  semantic_links: { definitions: SemanticRecord[]; disambiguations: SemanticRecord[] };
  support: {
    arguments: Array<{ id: string; meaning?: string; premise_statement_ids: string[]; conclusion_statement_id: string }>;
    results: Array<{ id: string; argument_id: string; theorem?: string }>;
    related_statements: Array<{ statement_id: string; lean_declaration: string; paraphrase: string; frontier_status: string }>;
  };
  coverage_notes: string[];
};
function record(value: unknown): value is Record<string, unknown> { return typeof value === "object" && value !== null && !Array.isArray(value); }
function strings(value: unknown): value is string[] { return Array.isArray(value) && value.every((item: unknown) => typeof item === "string"); }
function semantic(value: unknown): boolean { return record(value) && typeof value.id === "string" && (value.expression_ids === undefined || strings(value.expression_ids)); }
export function isExpressionNode(value: unknown, depth = 0): value is ExpressionNode {
  return depth < 120 && record(value) && ["id", "kind", "text", "type", "coverage"].every((key) => typeof value[key] === "string")
    && Array.isArray(value.children) && value.children.every((child: unknown) => record(child) && typeof child.role === "string" && isExpressionNode(child.node, depth + 1));
}
export function parseStructureReports(value: unknown): StructureReport[] {
  if (!record(value) || value.schema_version !== 1 || !Array.isArray(value.reports)) throw new Error("Invalid structure report bundle");
  for (const report of value.reports) {
    if (!record(report) || typeof report.statement_id !== "string" || typeof report.lean_declaration !== "string"
      || !record(report.revision) || typeof report.revision.head !== "string" || typeof report.revision.input_digest !== "string"
      || !Array.isArray(report.declarations) || !report.declarations.every((decl: unknown) => record(decl)
        && typeof decl.declaration === "string" && (decl.type === undefined || isExpressionNode(decl.type)) && (decl.expansion === undefined || isExpressionNode(decl.expansion)))
      || !record(report.semantic_links) || !Array.isArray(report.semantic_links.definitions) || !Array.isArray(report.semantic_links.disambiguations)
      || !record(report.support) || !Array.isArray(report.support.arguments) || !Array.isArray(report.support.results)
      || !Array.isArray(report.support.related_statements) || !strings(report.coverage_notes)
      || !report.semantic_links.definitions.every(semantic) || !report.semantic_links.disambiguations.every(semantic)
      || !report.support.arguments.every((argument: unknown) => record(argument) && typeof argument.id === "string" && strings(argument.premise_statement_ids) && typeof argument.conclusion_statement_id === "string")
      || !report.support.results.every((result: unknown) => record(result) && typeof result.id === "string" && typeof result.argument_id === "string")
      || !report.support.related_statements.every((statement: unknown) => record(statement) && ["statement_id", "lean_declaration", "paraphrase", "frontier_status"].every((key) => typeof statement[key] === "string"))) throw new Error("Invalid structure report");
  }
  return value.reports as StructureReport[];
}
let cached: StructureReport[] | undefined;
/** Disposable build input. This never invokes Lean during rendering or assigns proof status. */
export function getStructureReport(statementId: string): StructureReport | undefined {
  if (cached === undefined) {
    const root = path.resolve(process.cwd(), "../..");
    const artifact = path.resolve(root, process.env.TRUTH_CORE_STRUCTURE_REPORT ?? ".cache/proposition-structure.json");
    if (artifact !== path.join(root, ".cache/proposition-structure.json")) throw new Error("Structure report must use .cache/proposition-structure.json");
    if (!existsSync(artifact)) {
      if (process.env.TRUTH_CORE_REQUIRE_STRUCTURE_REPORT === "true") throw new Error("Structure input missing; run bun run structure-inputs");
      cached = [];
    }
    else {
      execFileSync("python3", ["scripts/corpus.py", "structure-report", "--check-input", "--output", artifact], { cwd: root, timeout: 60000, stdio: "pipe" });
      cached = parseStructureReports(JSON.parse(readFileSync(artifact, "utf8")));
    }
  }
  return cached.find((report) => report.statement_id === statementId);
}
