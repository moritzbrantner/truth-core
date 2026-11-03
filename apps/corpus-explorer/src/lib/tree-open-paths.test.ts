import { describe, expect, test } from "bun:test";

import { toggleOpenPath } from "./tree-open-paths";

describe("toggleOpenPath", () => {
  test("opens a branch and appends it after existing entries", () => {
    expect(toggleOpenPath(["root"], "root/A:0")).toEqual(["root", "root/A:0"]);
  });

  test("collapsing a branch also closes its descendants but not siblings with a shared prefix", () => {
    const open = ["root", "root/A:0", "root/A:0/B:1", "root/A:01"];
    expect(toggleOpenPath(open, "root/A:0")).toEqual(["root", "root/A:01"]);
  });

  test("collapsing the root clears every hidden entry", () => {
    expect(toggleOpenPath(["root", "root/A:0", "root/A:0/B:1"], "root")).toEqual([]);
  });

  test("drops entries whose ancestor is closed", () => {
    expect(toggleOpenPath(["root", "root/A:0/B:1"], "root/C:2")).toEqual(["root", "root/C:2"]);
  });

  test("bounds the encoded state by closing the oldest leaves and keeps the new branch", () => {
    const long = (index: number) => `root/ARGUMENT-WITH-A-LONG-IDENTIFIER-${index}:0`;
    let open = ["root"];
    for (let index = 0; index < 20; index += 1) { open = toggleOpenPath(open, long(index), 600); }
    const encoded = open.reduce((total, path) => total + "&open=".length + encodeURIComponent(path).length, 0);
    expect(encoded).toBeLessThanOrEqual(600);
    expect(open).toContain("root");
    expect(open).toContain(long(19));
    expect(open).not.toContain(long(0));
  });
});
