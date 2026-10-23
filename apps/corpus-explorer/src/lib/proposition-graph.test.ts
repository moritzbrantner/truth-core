import { describe, expect, test } from "bun:test";

import { buildPropositionGraph } from "./proposition-graph";
import { getPropositionGraph } from "./proposition-graph-data";
import { fixture } from "./proposition-graph.fixture";

describe("proposition graph status", () => {
  const graph = buildPropositionGraph(fixture);
  const byId = new Map(graph.statements.map((entry) => [entry.id, entry]));

  test("derives each status by the corpus.py frontier rules", () => {
    expect(byId.get("C")?.status).toBe("proved");
    expect(byId.get("ROOT")?.status).toBe("proved");
    expect(byId.get("TC")?.status).toBe("transcription");
    expect(byId.get("SE")?.status).toBe("self-evident");
    expect(byId.get("DEF")?.status).toBe("defended");
    expect(byId.get("ALT")?.status).toBe("alternative");
    expect(byId.get("ALT")?.refuted).toBe(true);
    expect(byId.get("OBJ")?.status).toBe("objection");
    expect(byId.get("P1")?.status).toBe("open");
    expect(byId.get("LONE")?.status).toBe("source-only");
  });

  test("marks the frontier: unproved, not self-evident, alternatives not all refuted", () => {
    const frontier = graph.statements.filter((entry) => entry.frontier).map((entry) => entry.id).sort();
    // ALT is refuted, but it is still a premise of the unverified A3; DEF is defended.
    // TC is proved only by a transcription (R4), so it stays open (invariant 16).
    expect(frontier).toEqual(["ALT", "P1", "P2", "T", "TC"]);
    expect(byId.get("TC")?.status).toBe("transcription");
    expect(byId.get("P1")?.transitiveDependentArguments).toBe(2);
  });

  test("derives tags from claims, namespaces, statuses and readings", () => {
    const p1 = byId.get("P1");
    expect(p1?.tags).toEqual(
      expect.arrayContaining(["source:SRC", "author:Aristotle", "ns:TruthCore.Test", "status:open", "frontier", "reading:A"]),
    );
    expect(byId.get("P2")?.tags).toContain("reading:B");
    expect(byId.get("ALT")?.tags).toEqual(expect.arrayContaining(["role:alternative", "role:refuted"]));
    expect(byId.get("OBJ")?.tags).toContain("role:objection");
    expect(byId.get("C")?.clusters).toEqual({
      passage: "derived · TruthCore.Test",
      source: "derived · TruthCore.Test",
      namespace: "TruthCore.Test",
    });
  });

  test("keeps only statement-to-statement relations as relation edges", () => {
    expect(graph.relations.map((relation) => relation.id)).toEqual(["REL1", "REL3"]);
  });

  test("falls back to the verified conclusion resting on the most statements", () => {
    expect(graph.rootPresent).toBe(false);
    expect(graph.defaultTarget).toBe("ROOT");
  });
});

describe("corpus proposition graph", () => {
  const graph = getPropositionGraph();

  test("covers every statement and inference with a default target", () => {
    expect(graph.statements.length).toBeGreaterThan(900);
    expect(graph.defaultTarget).not.toBeNull();
    expect(graph.statements.some((entry) => entry.status === "proved")).toBe(true);
    expect(graph.statements.some((entry) => entry.frontier)).toBe(true);
  });

  test("uses STMT-CATHOLICISM-TRUE as the default target once it exists", () => {
    const root = graph.statements.find((entry) => entry.id === "STMT-CATHOLICISM-TRUE");
    expect(graph.rootPresent).toBe(Boolean(root));
    if (root) {
      expect(graph.defaultTarget).toBe("STMT-CATHOLICISM-TRUE");
    }
  });
});
