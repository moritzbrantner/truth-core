import { expect, test } from "bun:test";

import { BELIEF_STORAGE_KEY, chooseBelief, readBeliefProfile, rejectBeliefs, writeBeliefProfile } from "./belief-profile";

const known = new Set(["P", "Q", "R"]);

test("versioned local beliefs round-trip, normalize duplicates and ignore unknown or corrupt records", () => {
  expect(BELIEF_STORAGE_KEY).toBe("truth-core:belief-profile:v1");
  const profile = readBeliefProfile(JSON.stringify({ version: 1, accepted: ["Q", "P", "P", "NOPE"], denied: ["Q", "R"] }), known);
  expect(profile).toEqual({ accepted: ["P", "Q"], denied: ["R"] });
  expect(readBeliefProfile(writeBeliefProfile(profile), known)).toEqual(profile);
  for (const raw of ["{bad", JSON.stringify({ version: 2, accepted: ["P"] }), JSON.stringify(["P"])]) {
    expect(readBeliefProfile(raw, known)).toEqual({ accepted: [], denied: [] });
  }
});

test("each explicit choice replaces the prior state; rejection preserves unaffected beliefs", () => {
  let profile = { accepted: ["P", "Q"], denied: ["R"] };
  profile = chooseBelief(profile, "R", "true");
  expect(profile).toEqual({ accepted: ["P", "Q", "R"], denied: [] });
  profile = chooseBelief(profile, "Q", "false");
  expect(profile).toEqual({ accepted: ["P", "R"], denied: ["Q"] });
  profile = rejectBeliefs(profile, ["R"]);
  expect(profile).toEqual({ accepted: ["P"], denied: ["Q"] });
  expect(chooseBelief(profile, "Q", "clear")).toEqual({ accepted: ["P"], denied: [] });
});
