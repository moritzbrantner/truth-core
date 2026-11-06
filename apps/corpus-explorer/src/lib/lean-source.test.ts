import { describe, expect, test } from "bun:test";

import { indexLeanSource, leanIndex, pinnedCoreLocations } from "./lean-source";

describe("Lean source locations", () => {
  test("resolves raw core Nonempty to its inspected pinned official source", () => {
    const location = leanIndex().get("Nonempty");
    expect(location?.name).toBe("Nonempty");
    expect(location?.file).toBe("src/Init/Prelude.lean");
    expect(location?.line).toBe(839);
    expect(location?.sourceUrl).toBe("https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/Prelude.lean#L839");
    expect(pinnedCoreLocations("leanprover/lean4:v0.0.0")).toEqual([]);
  });

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

  test("locates directly declared fields at their field lines, retaining top-level declarations", () => {
    const source = [
      "namespace Outer",
      "  namespace Inner",
      "    structure Frame where",
      "      /-- The supplied carrier. -/",
      "      Being : Type",
      "      predicate : Being → Prop := fun _ =>",
      "        let localValue : Prop := True",
      "        localValue",
      "    def after : Nat := 1",
      "  end Inner",
      "  structure Other where",
      "    value : Nat",
      "end Outer",
    ].join("\n");
    const locations = indexLeanSource("Fixture.lean", source);
    expect(locations.map(({ name, line }) => ({ name, line }))).toEqual([
      { name: "Outer.Inner.Frame", line: 3 },
      { name: "Outer.Inner.Frame.Being", line: 5 },
      { name: "Outer.Inner.Frame.predicate", line: 6 },
      { name: "Outer.Inner.after", line: 9 },
      { name: "Outer.Other", line: 11 },
      { name: "Outer.Other.value", line: 12 },
    ]);
    expect(locations[1].snippet).toBe("      /-- The supplied carrier. -/\n      Being : Type");
    expect(locations[2].snippet).not.toContain("def after");
    expect(locations.some(({ name }) => name.endsWith(".localValue"))).toBe(false);
  });

  test("handles multiline structure headers and does not invent inherited field locations", () => {
    const source = [
      "namespace Example",
      "structure Base where",
      "  inherited : Nat",
      "structure Derived",
      "    extends Base where",
      "  mk ::",
      "  /- Ignore a fake field: fake : Nat -/",
      "  extra : Nat",
      "  /- A multiline comment",
      "  notAField : Nat",
      "  -/",
      "  last : Bool",
      "end Example",
    ].join("\n");
    const locations = indexLeanSource("Fixture.lean", source);
    expect(locations.map(({ name }) => name)).toEqual([
      "Example.Base", "Example.Base.inherited", "Example.Derived",
      "Example.Derived.extra", "Example.Derived.last",
    ]);
  });

  test("resolves the actual field projections used by the definition-pointer repair", () => {
    const index = leanIndex();
    const fields = [
      ["TruthCore.Latin.Aquinas.SummaTheologiae.MotionModel.InAct", "InAct : Being → Respect → Prop"],
      ["TruthCore.Latin.Aquinas.SummaTheologiae.MotionModel.Being", "Being : Type"],
      ["TruthCore.Latin.Aquinas.SummaTheologiae.MotionModel.Respect", "Respect : Type"],
      ["TruthCore.Latin.Aquinas.SummaTheologiae.MotionModel.MovedIn", "MovedIn : Being → Respect → Prop"],
      ["TruthCore.Case.Catholicism.Signature.IsGod", "IsGod : Being → Prop"],
      ["TruthCore.Greek.Plato.ParticipationGrounding.Explanation.Grounds", "Grounds : Fact Entity Quality Feature → Fact Entity Quality Feature → Prop"],
      ["TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile.essenceOf", "essenceOf : Being → Principle"],
    ];
    for (const [name, field] of fields) {
      const location = index.get(name);
      expect(location?.name).toBe(name);
      expect(location?.snippet).toContain(field);
      expect(location?.snippet).not.toContain("structure ");
      expect(location?.line).toBeGreaterThan(0);
    }
  });
});
