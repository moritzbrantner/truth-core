import { fixtureGraph } from "./frontier-fixture";
import { describe, expect, test } from "bun:test";
import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

import { type PropositionGraphInput } from "./proposition-graph";
import { getPropositionGraph } from "./proposition-graph-data";
import { fixture } from "./proposition-graph.fixture";

describe("proposition graph status", () => {
  const graph = fixtureGraph(fixture);
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

  test("classifies open premises as bare or sourced, as corpus.py frontier does", () => {
    const depths = Object.fromEntries(
      graph.statements.filter((entry) => entry.frontier).map((entry) => [entry.id, entry.frontierDepth]),
    );
    // P1/P2 are stated by claims; T has a supports relation; ALT and TC have neither.
    expect(depths).toEqual({ ALT: "bare", P1: "sourced", P2: "sourced", T: "sourced", TC: "bare" });
    expect(byId.get("T")?.tags).toContain("frontier:sourced");
    expect(byId.get("TC")?.tags).toContain("frontier:bare");
    expect(byId.get("C")?.frontierDepth).toBeUndefined();
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

  test("projects recorded claim and argument links through their statement without treating them as inference", () => {
    expect(graph.relations.map((relation) => [relation.id, relation.subject, relation.object, relation.originKind, relation.originId])).toEqual([
      ["REL1", "ALT", "DEF", "statement", "ALT"],
      ["REL2", "NALT", "ALT", "argument", "A6"],
      ["REL3", "OBJ", "C", "statement", "OBJ"],
      ["REL4", "LONE", "T", "claim", "CL-LONE"],
    ]);
    expect(graph.inferences).toHaveLength(fixture.inferences.length);
    expect(graph.relations.find((relation) => relation.id === "REL4")?.note).toBe("Source evidence, not a proof step.");
  });

  test("falls back to the verified conclusion resting on the most statements", () => {
    expect(graph.rootPresent).toBe(false);
    expect(graph.defaultTarget).toBe("ROOT");
  });
});

describe("rule (d): transcription from closed premises", () => {
  // Shared with scripts/test_corpus_frontier.py so both implementations agree.
  const shared = JSON.parse(
    readFileSync(
      fileURLToPath(new URL("../../../../scripts/testdata/frontier-transcription-closure.json", import.meta.url)),
      "utf8",
    ),
  ) as Omit<PropositionGraphInput, "sources" | "inferences" | "transcriptionResultIds"> & {
    transcription_result_ids: string[];
    expected_frontier: string[];
    expected_depth: Record<string, string>;
    expected_closed_via_transcription: Record<string, string>;
  };
  const input: PropositionGraphInput = {
    statements: shared.statements,
    arguments: shared.arguments,
    results: shared.results,
    relations: shared.relations,
    claims: shared.claims,
    sources: [],
    inferences: [],
    transcriptionResultIds: shared.transcription_result_ids,
  };

  test("matches the corpus.py frontier on the shared parity fixture", () => {
    for (const reversed of [false, true]) {
      const order = <T,>(items: T[]) => (reversed ? [...items].reverse() : items);
      const graph = fixtureGraph({
        ...input,
        statements: order(input.statements),
        arguments: order(input.arguments),
        results: order(input.results),
        relations: order(input.relations),
        claims: order(input.claims),
      });
      const frontier = graph.statements.filter((entry) => entry.frontier).map((entry) => entry.id).sort();
      expect(frontier).toEqual(shared.expected_frontier);
      expect(
        Object.fromEntries(graph.statements.filter((entry) => entry.frontier).map((entry) => [entry.id, entry.frontierDepth])),
      ).toEqual(shared.expected_depth);
      const closures = Object.fromEntries(
        graph.statements.flatMap((entry) =>
          entry.closedViaTranscription ? [[entry.id, entry.closedViaTranscription.resultId]] : [],
        ),
      );
      expect(closures).toEqual(shared.expected_closed_via_transcription);
    }
  });

  test("keeps the transcription status and tags the closure", () => {
    const t2 = fixtureGraph(input).statements.find((entry) => entry.id === "T2");
    expect(t2?.status).toBe("transcription");
    expect(t2?.tags).toContain("closed:transcription-from-closed-premises");
    expect(t2?.closedViaTranscription).toEqual({ resultId: "R-A-T2", argumentId: "ARG-T2", premises: ["T1"] });
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

  test("closes the excluded-middle instances via transcription from closed premises", () => {
    const byId = new Map(graph.statements.map((entry) => [entry.id, entry]));
    for (const id of ["STMT-FIRST-UNMOVED-MOVER-EXISTS-OR-NOT", "STMT-FIRST-UNMOVED-MOVERS-IDENTICAL-OR-DISTINCT"]) {
      expect(byId.get(id)?.frontier).toBe(false);
      expect(byId.get(id)?.closedViaTranscription?.premises).toEqual(["STMT-EXCLUDED-MIDDLE"]);
    }
    // A bridge transcription whose bridge premise is open stays open.
    expect(byId.get("STMT-TIME-IS-NOT-MOTION")?.frontier).toBe(true);
  });

  test("has the same frontier and closures as corpus.py frontier", () => {
    const repositoryRoot = fileURLToPath(new URL("../../../../", import.meta.url));
    const report = JSON.parse(
      execFileSync("python3", ["scripts/corpus.py", "frontier", "--json"], { cwd: repositoryRoot, encoding: "utf8" }),
    ) as {
      items: Array<{ statement_id: string; depth: string }>;
      closed_via_transcription: Array<{ statement_id: string; result_id: string }>;
    };
    const frontier = graph.statements.filter((entry) => entry.frontier).map((entry) => entry.id).sort();
    expect(frontier).toEqual(report.items.map((item) => item.statement_id).sort());
    const depths = Object.fromEntries(
      graph.statements.filter((entry) => entry.frontier).map((entry) => [entry.id, entry.frontierDepth]),
    );
    expect(depths).toEqual(Object.fromEntries(report.items.map((item) => [item.statement_id, item.depth])));
    const closures = graph.statements
      .flatMap((entry) => (entry.closedViaTranscription ? [`${entry.id}:${entry.closedViaTranscription.resultId}`] : []))
      .sort();
    expect(closures).toEqual(report.closed_via_transcription.map((item) => `${item.statement_id}:${item.result_id}`).sort());
  });

  test("uses STMT-CATHOLICISM-TRUE as the default target once it exists", () => {
    const root = graph.statements.find((entry) => entry.id === "STMT-CATHOLICISM-TRUE");
    expect(graph.rootPresent).toBe(Boolean(root));
    if (root) {
      expect(graph.defaultTarget).toBe("STMT-CATHOLICISM-TRUE");
    }
  });
});
