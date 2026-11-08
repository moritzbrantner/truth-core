import { expect, test } from "bun:test";

import { legacyUuid, shortId } from "./corpus-ids";

test("legacyUuid reproduces the Python uuid5 migration", () => {
  expect(legacyUuid("statement", "STMT-CATHOLICISM-TRUE")).toBe("53964cbe-5831-5812-af33-4d87896d47a7");
  expect(legacyUuid("result", "ABSENT-ONLY-UNIVERSE-CAUSERS-DEFEAT-ACTUALITY-POLICY")).not.toBe(
    legacyUuid("argument", "ABSENT-ONLY-UNIVERSE-CAUSERS-DEFEAT-ACTUALITY-POLICY"),
  );
  expect(legacyUuid("argument", "ABSENT-ONLY-UNIVERSE-CAUSERS-DEFEAT-ACTUALITY-POLICY")).toBe(
    "5758bd1a-bcde-514a-9d60-cf363e3a6915",
  );
  expect(shortId("53964cbe-5831-5812-af33-4d87896d47a7")).toBe("53964cbe");
});
