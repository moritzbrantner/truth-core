import { describe, expect, test } from "bun:test";

import {
  projectArgumentComposition,
  type ArgumentProjectionCorpus,
} from "./argument-projection";

const corpus: ArgumentProjectionCorpus = {
  statements: [
    { id: "A", paraphrase: "A" },
    { id: "B", paraphrase: "B" },
    { id: "C", paraphrase: "C" },
    { id: "D", paraphrase: "D" },
  ],
  inferences: [
    { id: "I1", input_statement_ids: ["A", "B"], output_statement_id: "C", rule: "modus-ponens", meaning: "A and B support C." },
    { id: "I2", input_statement_ids: ["D"], output_statement_id: "A", rule: "support", meaning: "D supports A." },
  ],
  arguments: [
    { id: "ARG1", premise_statement_ids: ["A", "B"], conclusion_statement_id: "C", inference_ids: ["I1"], meaning: "C follows." },
    { id: "ARG2", premise_statement_ids: ["D"], conclusion_statement_id: "A", inference_ids: ["I2"], meaning: "A follows." },
  ],
  verified_argument_ids: ["ARG1", "ARG2"],
};

describe("argument projection", () => {
  test("keeps a collapsed root as one reusable argument block", () => {
    const projection = projectArgumentComposition(corpus, "ARG1", new Set());

    expect(projection.nodes.map((node) => node.argumentId)).toEqual(["ARG1"]);
    expect(projection.nodes[0].expanded).toBe(false);
    expect(projection.edges).toHaveLength(0);
  });

  test("reveals supporting arguments when their consumer is expanded", () => {
    const projection = projectArgumentComposition(corpus, "ARG1", new Set(["ARG1"]));

    expect(projection.nodes.map((node) => node.argumentId)).toEqual(["ARG2", "ARG1"]);
    expect(projection.nodes.find((node) => node.argumentId === "ARG2")?.expanded).toBe(false);
    expect(projection.edges).toEqual([
      { id: "ARG2->ARG1:A", source: "ARG2", target: "ARG1", statementId: "A", cycle: false },
    ]);
  });

  test("cuts recursive expansion at cycles while retaining a back-reference edge", () => {
    const cyclicCorpus: ArgumentProjectionCorpus = {
      statements: [{ id: "A", paraphrase: "A" }, { id: "B", paraphrase: "B" }],
      inferences: [
        { id: "AB", input_statement_ids: ["A"], output_statement_id: "B", rule: "forward", meaning: "A supports B." },
        { id: "BA", input_statement_ids: ["B"], output_statement_id: "A", rule: "reverse", meaning: "B supports A." },
      ],
      arguments: [
        { id: "ARG-AB", premise_statement_ids: ["A"], conclusion_statement_id: "B", inference_ids: ["AB"], meaning: "B from A." },
        { id: "ARG-BA", premise_statement_ids: ["B"], conclusion_statement_id: "A", inference_ids: ["BA"], meaning: "A from B." },
      ],
      verified_argument_ids: ["ARG-AB", "ARG-BA"],
    };

    const projection = projectArgumentComposition(
      cyclicCorpus,
      "ARG-AB",
      new Set(["ARG-AB", "ARG-BA"]),
    );

    expect(projection.nodes).toHaveLength(2);
    expect(projection.edges).toHaveLength(2);
    expect(projection.edges.some((edge) => edge.cycle)).toBe(true);
  });
});
