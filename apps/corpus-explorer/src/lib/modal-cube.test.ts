import { describe, expect, test } from "bun:test";

import {
  MODAL_SYSTEMS,
  buildWitnessFrame,
  closeAxioms,
  detectFrameConditions,
  modalTruthAt,
} from "./modal-cube";

describe("modal cube", () => {
  test("S5 closes T and 5 to all optional cube axioms", () => {
    expect([...closeAxioms(["T", "5"])].sort()).toEqual(["4", "5", "B", "D", "T"]);
  });

  test("B plus 5 implies 4", () => {
    expect(closeAxioms(["B", "5"]).has("4")).toBe(true);
  });

  test("the generated S4 witness is reflexive and transitive but not symmetric", () => {
    const s4 = MODAL_SYSTEMS.find((system) => system.id === "S4");
    if (!s4) throw new Error("S4 must exist");

    const conditions = detectFrameConditions(buildWitnessFrame(s4));
    expect(conditions.has("reflexive")).toBe(true);
    expect(conditions.has("serial")).toBe(true);
    expect(conditions.has("transitive")).toBe(true);
    expect(conditions.has("symmetric")).toBe(false);
  });

  test("the default Lean example changes modal perspective", () => {
    const s4 = MODAL_SYSTEMS.find((system) => system.id === "S4");
    if (!s4) throw new Error("S4 must exist");

    const edges = buildWitnessFrame(s4);
    const valuation = { actual: false, nearby: false, remote: true };

    expect(modalTruthAt("actual", edges, valuation)).toMatchObject({
      p: false,
      possibleP: true,
      necessaryP: false,
    });
    expect(modalTruthAt("remote", edges, valuation)).toMatchObject({
      p: true,
      possibleP: true,
      necessaryP: true,
    });
  });
});
