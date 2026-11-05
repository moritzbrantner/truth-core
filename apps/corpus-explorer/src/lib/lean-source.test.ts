import { describe, expect, test } from "bun:test";

import { indexLeanSource, leanIndex, pinnedCoreLocations } from "./lean-source";

describe("Lean source locations", () => {
  test("resolves raw core WellFounded to its inspected pinned official source", () => {
    const location = leanIndex().get("WellFounded");
    expect(location?.name).toBe("WellFounded");
    expect(location?.file).toBe("src/Init/WF.lean");
    expect(location?.line).toBe(60);
    expect(location?.sourceUrl).toBe("https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/WF.lean#L60");
    expect(pinnedCoreLocations("leanprover/lean4:v0.0.0")).toEqual([]);
  });

  test("indexes an indented theorem without including the next declaration", () => {
    const source = [
      "namespace Example",
      " /-- First proof. -/",
      " @[simp]",
      " theorem first : True := by",
      "   trivial",
      "",
      " theorem second : True := by",
      "   trivial",
      "end Example",
    ].join("\n");
    const locations = indexLeanSource("Fixture.lean", source);
    expect(locations.map(({ name, line }) => ({ name, line }))).toEqual([
      { name: "Example.first", line: 4 },
      { name: "Example.second", line: 7 },
    ]);
    expect(locations[0].snippet).toBe(" /-- First proof. -/\n @[simp]\n theorem first : True := by\n   trivial");
    expect(locations[1].snippet).toBe(" theorem second : True := by\n   trivial");
  });

  test("qualifies declarations inside indented namespace boundaries", () => {
    const source = [
      "namespace Outer",
      "  namespace Inner",
      "    def P : Prop := True",
      "  end Inner",
      "  theorem outerProof : True := by",
      "    trivial",
      "end Outer",
    ].join("\n");
    expect(indexLeanSource("Fixture.lean", source).map(({ name }) => name)).toEqual([
      "Outer.Inner.P",
      "Outer.outerProof",
    ]);
  });
});
