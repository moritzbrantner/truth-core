import { expect, test } from "bun:test";
import { parseStructureReports } from "./proposition-structure";

const atom = (text: string) => ({ id: text, kind: "variable", text, type: "Entity", coverage: "complete", children: [] });
const application = (args: string[]) => ({ id: "P", kind: "application", text: `P ${args.join(" ")}`, type: "Prop", coverage: "complete", children: [
  { role: "function", node: { ...atom("P"), kind: "constant", type: "Entity → Entity → Prop" } },
  ...args.map((arg, i) => ({ role: `argument.${i}`, node: atom(arg) })),
] });
function bundle(expression = application(["a", "b"])) {
  return { schema_version: 1, reports: [{ statement_id: "STMT-TEST", lean_declaration: "Test.P", revision: { head: "abc", input_digest: "digest" }, declarations: [{ declaration: "Test.P", type: expression }], semantic_links: { definitions: [], disambiguations: [] }, support: { arguments: [], results: [], related_statements: [] }, coverage_notes: [] }] };
}

test("transport retains application order and readable expressions", () => {
  const first = parseStructureReports(bundle())[0].declarations[0].type!;
  const second = parseStructureReports(bundle(application(["b", "a"])))[0].declarations[0].type!;
  expect(first.children.map(({ node }) => node.text)).toEqual(["P", "a", "b"]);
  expect(second.children.map(({ node }) => node.text)).toEqual(["P", "b", "a"]);
  expect(first).not.toEqual(second);
});

test("transport preserves explicit partial coverage without atom reinterpretation", () => {
  const input = bundle();
  input.reports[0].declarations[0].type = { ...application([]), kind: "unsupported", coverage: "partial: depth limit", children: [] };
  const result = parseStructureReports(input)[0].declarations[0].type!;
  expect(result.kind).toBe("unsupported");
  expect(result.coverage).toBe("partial: depth limit");
});

test("transport rejects missing nested structure instead of silently accepting it", () => {
  const input = bundle();
  Reflect.deleteProperty(input.reports[0].declarations[0].type.children[0].node, "type");
  expect(() => parseStructureReports(input)).toThrow("Invalid structure report");
});
