import { fixtureGraph, type GraphFixtureInput } from "./frontier-fixture";
import { describe, expect, test } from "bun:test";
import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

import { type PropositionGraphInput } from "./proposition-graph";
import { getPropositionGraph } from "./proposition-graph-data";
import { fixture } from "./proposition-graph.fixture";
import { getDossiers } from "./premise-dossier";
import { getFrontierReport, statementState, type FrontierReport } from "./site-state";

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

  test("takes the default target and root presence from the report", () => {
    expect(graph.rootPresent).toBe(true);
    expect(graph.defaultTarget).toBe("ROOT");
  });

  test("labels a floor marking self-evident only while its basis criterion holds", () => {
    expect(byId.get("SE")?.floor).toMatchObject({ basis: "legacy", met: true });
    const unmet = fixtureGraph({
      ...fixture,
      statements: fixture.statements.map((entry) =>
        entry.id === "SE"
          ? { ...entry, self_evident: { justification_ids: ["CL-LONE"], basis: "observation", disagreement: "none recorded" } }
          : entry,
      ),
    });
    const se = unmet.statements.find((entry) => entry.id === "SE");
    expect(se?.status).toBe("open");
    expect(se?.frontier).toBe(true);
    expect(se?.closureReason).toBeUndefined();
    expect(se?.floor).toMatchObject({ basis: "observation", met: false, reasons: ["no justification claim states it"] });
  });
});

describe("rule (d): transcription from closed premises", () => {
  // Shared with scripts/test_corpus_frontier.py so both implementations agree.
  const shared = JSON.parse(
    readFileSync(
      fileURLToPath(new URL("../../../../scripts/testdata/frontier-transcription-closure.json", import.meta.url)),
      "utf8",
    ),
  ) as Omit<PropositionGraphInput, "sources" | "inferences"> & {
    transcription_result_ids: string[];
    expected_frontier: string[];
    expected_depth: Record<string, string>;
    expected_closed_via_transcription: Record<string, string>;
  };
  const input: GraphFixtureInput = {
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

  // The single guard of #507: what the explorer displays for closure and floor
  // status (graph, statement pages, dossiers) equals an independent run of
  // `corpus.py frontier --json` on the real corpus, statement by statement.
  test("displays the closure and floor status of corpus.py frontier --json", () => {
    const repositoryRoot = fileURLToPath(new URL("../../../../", import.meta.url));
    const report = JSON.parse(
      execFileSync("python3", ["scripts/corpus.py", "frontier", "--json"], {
        cwd: repositoryRoot,
        encoding: "utf8",
        maxBuffer: 64 * 1024 * 1024,
      }),
    ) as FrontierReport;
    const items = new Map(report.items.map((item) => [item.statement_id, item]));
    const transcribed = new Map(report.closed_via_transcription.map((entry) => [entry.statement_id, entry.result_id]));
    const floor = new Map(report.floor.map((entry) => [entry.statement_id, entry]));
    const established = new Set(report.established_statements);
    const expected = (id: string) => ({
      status: report.statement_statuses[id],
      closure: report.closed_statements[id] ?? null,
      established: established.has(id),
      depth: items.get(id)?.depth ?? null,
      transcribedBy: transcribed.get(id) ?? null,
      floor: floor.get(id) ?? null,
    });
    const shown = getFrontierReport();
    const dossiers = getDossiers();
    const displayed = (statement: (typeof graph.statements)[number]) => {
      const state = statementState(shown, statement.id);
      const dossier = dossiers[statement.id];
      // Every view must agree before it counts as displayed.
      expect([state.kind === "closed" ? state.reason : null, dossier?.closure ?? null, dossier?.established ?? false]).toEqual([
        statement.closureReason ?? null,
        statement.closureReason ?? null,
        statement.established,
      ]);
      expect(state.kind === "open" ? state.item.depth : null).toBe(statement.frontierDepth ?? null);
      return {
        status: statement.status,
        closure: statement.closureReason ?? null,
        established: statement.established,
        depth: statement.frontier ? (statement.frontierDepth ?? null) : null,
        transcribedBy: statement.closedViaTranscription?.resultId ?? null,
        floor: statement.floor ?? null,
      };
    };
    expect(graph.statements.map((statement) => statement.id).sort()).toEqual(Object.keys(report.statement_statuses).sort());
    for (const statement of graph.statements) {
      expect({ id: statement.id, ...displayed(statement) }).toEqual({ id: statement.id, ...expected(statement.id) });
    }
  });

  test("uses STMT-CATHOLICISM-TRUE as the default target once it exists", () => {
    const root = graph.statements.find((entry) => entry.id === "STMT-CATHOLICISM-TRUE");
    expect(graph.rootPresent).toBe(Boolean(root));
    if (root) {
      expect(graph.defaultTarget).toBe("STMT-CATHOLICISM-TRUE");
    }
  });
});
