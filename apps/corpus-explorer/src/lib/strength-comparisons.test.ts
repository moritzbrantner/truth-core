import { expect, test } from "bun:test";
import { comparisonsForResult, comparisonsForStatement, parseStrengthComparisons } from "./strength-comparisons";

function bundle() {
  const proof = (role: string) => ({ role, result_id: `RESULT-${role}`, theorem: `Proof.${role}`, argument_id: `ARG-${role}`, bound: true as const, expected_type: `${role} expected`, actual_type: `${role} actual` });
  return {
    schema_version: 2, producer: { mode: "live-verified", input_digest: "current-inputs" }, comparisons: [{
      id: "REL-COMPARE", stronger_statement_id: "STMT-S", weaker_statement_id: "STMT-W", delta_statement_id: "STMT-D", remainder_statement_id: "STMT-R",
      background_statement_ids: ["STMT-GAMMA"], comparison_spec: "Comparison.spec", note: "Selected background comparison.", verified: true,
      comparison_status: "strict strengthening", converse_status: "refuted by separating setting", delta_status: "exact factorization proved",
      explanatory_status: "reviewed interpretation; informative explanation is not certified by factorization",
      explanatory_controls: [{ result_id: "CONTROL", argument_id: "ARG-CONTROL", theorem: "Proof.control", description: "Explanation control." }],
      obligations: ["implication", "delta_forward", "reconstruction", "equivalence"].map(proof),
      binding: { field_bindings: ["stronger", "weaker", "delta", "background.0", "remainder"].map((role) => ({ role, declaration: "Decl", parameter_indices: [0], expected_application: "Decl x", explicit_application: "Decl x", expression: "Decl x", type: "Prop", bound: true })), parameters: [{ name: "x", type: "Entity" }], formulas: { background: ["G x"], stronger: "S x", weaker: "W x", delta: "D x", remainder: "W x ∧ ¬ S x" } },
      separator: { setting: "Concrete.setting", result_id: "RESULT-SEPARATOR", theorem: "Proof.separator", bound: true },
      remaining_obligations: [], definitions: [], disambiguations: [],
      provenance: { result_ids: ["RESULT-implication", "RESULT-SEPARATOR"], bind_check: "bound", semantic_binding: "definitional equality", comparator: "passed" }, scope_notes: ["No minimality claim."],
    }],
  };
}

test("certified transport preserves background, added requirement and allowed cases separately", () => {
  const input = parseStrengthComparisons(bundle());
  expect(input[0].binding.formulas).toEqual({ background: ["G x"], stronger: "S x", weaker: "W x", delta: "D x", remainder: "W x ∧ ¬ S x" });
  expect(comparisonsForStatement(input, "STMT-GAMMA")).toHaveLength(1);
  expect(comparisonsForStatement(input, "STMT-R")).toHaveLength(1);
  expect(comparisonsForStatement(input, "UNRELATED")).toHaveLength(0);
  expect(comparisonsForResult(input, "RESULT-SEPARATOR")).toHaveLength(1);
  expect(comparisonsForResult(input, "CONTROL")).toHaveLength(1);
});

test("strictness without checked separating evidence is rejected", () => {
  const input = bundle();
  Reflect.deleteProperty(input.comparisons[0], "separator");
  expect(() => parseStrengthComparisons(input)).toThrow("lacks its certified evidence");
});

test("a sufficient delta cannot be relabelled as exact when reconstruction is missing", () => {
  const input = bundle();
  input.comparisons[0].obligations = input.comparisons[0].obligations.filter((entry) => entry.role !== "reconstruction");
  expect(() => parseStrengthComparisons(input)).toThrow("lacks its certified evidence");
  input.comparisons[0].delta_status = "sufficient only; exactness unresolved";
  expect(parseStrengthComparisons(input)[0].delta_status).toBe("sufficient only; exactness unresolved");
});

test("S iff W-and-D does not certify S iff W or resolve its converse", () => {
  const input = bundle();
  input.comparisons[0].comparison_status = "proved equivalence";
  expect(() => parseStrengthComparisons(input)).toThrow("lacks its certified evidence");
});

test("a named allowed case needs both decomposition and admitted-only identity", () => {
  const input = bundle();
  Object.assign(input.comparisons[0], { remainder_status: "exact admitted-only remainder proved" });
  expect(() => parseStrengthComparisons(input)).toThrow("lacks its certified evidence");
});

test("unbound or registration-only reports never receive certified presentation", () => {
  const input = bundle();
  input.comparisons[0].obligations[0].bound = false as unknown as true;
  expect(() => parseStrengthComparisons(input)).toThrow("Invalid certified comparison");
  const registered = bundle();
  registered.producer.mode = "registered";
  expect(() => parseStrengthComparisons(registered)).toThrow("Invalid certified comparison bundle");
});

test("partial structural evidence stays explicit, without invented primitive semantics", () => {
  const input = bundle();
  Object.assign(input.comparisons[0].binding, { structure: [{ declaration: "Comparison.spec", expansion: { id: "cut", kind: "unsupported", text: "some expression", type: "Prop", coverage: "partial: depth limit", children: [] } }] });
  const report = parseStrengthComparisons(input)[0];
  expect(report.binding.structure?.[0].expansion?.kind).toBe("unsupported");
  expect(report.binding.structure?.[0].expansion?.coverage).toContain("partial");
});

test("failed or head-only field binding cannot receive a displayed verdict", () => {
  const input = bundle();
  input.comparisons[0].binding.field_bindings[0].bound = false;
  expect(() => parseStrengthComparisons(input)).toThrow("complete statement application");
  Reflect.deleteProperty(input.comparisons[0].binding.field_bindings[0], "expected_application");
  input.comparisons[0].binding.field_bindings[0].bound = true;
  expect(() => parseStrengthComparisons(input)).toThrow("complete statement application");
});
