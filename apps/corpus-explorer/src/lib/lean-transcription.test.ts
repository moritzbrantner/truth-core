import { describe, expect, test } from "bun:test";

import { getCorpus } from "./corpus";
import { singleApplicationOf, transcriptionFlags } from "./lean-transcription";

const header = `theorem bridged
    {Entity : Type}
    (P Q : Entity → Prop)
    (a : Entity)
    -- a comment mentioning hBridge
    (hBridge : ∀ x, P x → Q x)
    (hP : P a) :
    Q a := by`;

describe("transcription heuristic", () => {
  test("flags a proof that only applies one hypothesis", () => {
    expect(singleApplicationOf(`${header}\n  exact hBridge a hP\n`, "bridged")).toBe("hBridge");
    expect(singleApplicationOf(`${header}\n  intro\n  exact hBridge a hP\n`, "bridged")).toBe("hBridge");
    expect(singleApplicationOf(`${header.replace(":= by", ":=")}\n  hBridge a hP\n`, "bridged")).toBe("hBridge");
    expect(singleApplicationOf(`${header.replace(":= by", ":=")}\n  hBridge\n    a\n    hP\n`, "bridged")).toBe("hBridge");
  });

  test("does not flag multi-step proofs or applications of lemmas", () => {
    expect(singleApplicationOf(`${header}\n  have h := hBridge a hP\n  exact h\n`, "bridged")).toBeNull();
    expect(singleApplicationOf(`${header}\n  exact someLemma hBridge hP\n`, "bridged")).toBeNull();
    expect(singleApplicationOf(`${header}\n  exact hBridge a hP\n`, "other")).toBeNull();
  });

  test("reads the corpus Solution modules at build time", () => {
    const corpus = getCorpus();
    const flagged = new Set(transcriptionFlags(corpus.results).map((flag) => flag.resultId));

    // cosmosHasCause is `exact hCause cosmos hCosmos`.
    expect(flagged.has("PLATO-TIM-28A-28C-COSMOS-CAUSE-A")).toBe(true);
    expect(flagged.size).toBeLessThan(corpus.results.length);
  });
});
