import { describe, expect, test } from "bun:test";

import { layeredLayout } from "./graph-layout";

const node = (id: string) => ({ id, width: 100, height: 40 });

describe("layered layout", () => {
  test("places premises below inferences and conclusions above", () => {
    const positions = layeredLayout(
      [node("P1"), node("P2"), node("I"), node("C")],
      [
        { source: "P1", target: "I" },
        { source: "P2", target: "I" },
        { source: "I", target: "C" },
      ],
    );
    const y = (id: string) => positions.get(id)?.y ?? Number.NaN;
    expect(y("C")).toBeLessThan(y("I"));
    expect(y("I")).toBeLessThan(y("P1"));
    expect(y("P1")).toBe(y("P2"));
    expect(positions.get("P1")?.x).not.toBe(positions.get("P2")?.x);
  });

  test("lifts a premise to just below its consumer", () => {
    const positions = layeredLayout(
      [node("A"), node("I1"), node("B"), node("I2"), node("C"), node("late")],
      [
        { source: "A", target: "I1" },
        { source: "I1", target: "B" },
        { source: "B", target: "I2" },
        { source: "late", target: "I2" },
        { source: "I2", target: "C" },
      ],
    );
    expect(positions.get("late")?.y).toBe(positions.get("B")?.y);
  });

  test("lays out cycles without looping", () => {
    const positions = layeredLayout(
      [node("A"), node("B")],
      [
        { source: "A", target: "B" },
        { source: "B", target: "A" },
      ],
    );
    expect(positions.size).toBe(2);
    expect(positions.get("A")?.y).not.toBe(positions.get("B")?.y);
  });

  test("wraps a wide layer into rows", () => {
    const many = Array.from({ length: 10 }, (_, index) => node(`N${index}`));
    const positions = layeredLayout(many, [], { maxRowWidth: 450, nodeGap: 10 });
    const rows = new Set([...positions.values()].map((point) => point.y));
    expect(rows.size).toBe(3);
  });
});
