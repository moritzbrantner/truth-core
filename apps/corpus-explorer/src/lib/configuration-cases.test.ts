import { expect, test } from "bun:test";

import { parseRegisteredConfigurationCases } from "./configuration-cases";

test("static configuration provenance rejects live status or malformed settings", () => {
  const configuration = {
    id: "CONFIG-TEST", seed_statement_id: "STMT-P", verified: false, inapplicable_models: [], scope: "registered only",
    semantics: { id: "P", logic: "constructive", frame: "arbitrary", domain: "fixed", identity: "literal", vocabulary: "V" },
    configurations: [{ id: "control", statement_ids: ["STMT-P"], status: "verification required", incompatible_cores: [], model_ids: [] }],
  };
  expect(parseRegisteredConfigurationCases([configuration])).toEqual([configuration]);
  expect(() => parseRegisteredConfigurationCases([{ ...configuration, verified: true }])).toThrow();
  expect(() => parseRegisteredConfigurationCases([{ ...configuration, semantics: {} }])).toThrow();
  expect(() => parseRegisteredConfigurationCases([{ ...configuration, configurations: [{ ...configuration.configurations[0], status: "model witnessed" }] }])).toThrow();
});
