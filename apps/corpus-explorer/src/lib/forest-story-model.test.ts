import { expect, test } from "bun:test";
import { forestCoverage, forestPaths } from "../../tests/forest-story-model";

test("argument-forest browser model retains its reviewed bounded coverage", () => {
  // The generator verifies every declared edge, including reload self-loops.
  expect(forestCoverage).toEqual({ states: 3, transitions: 8, paths: 6 });
  const paths = forestPaths();
  expect(new Set(paths.map((path) => path.name)).size).toBe(paths.length);
  expect(paths.map((path) => path.name)).toContain("SELECT > EXPLORE_NEGATION > RELOAD");
  expect(paths.map((path) => path.name)).toContain("SELECT > EXPLORE_NEGATION > RETURN");
});
