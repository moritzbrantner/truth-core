import { expect, test } from "bun:test";
import { createElement } from "react";
import { renderToStaticMarkup } from "react-dom/server";

import type { CorpusAttempt } from "@/lib/premise-dossier";

import { DossierAttemptIndex } from "./dossier-attempt-index";

test("dossier attempt links keep stable anchors without duplicating long research logs", () => {
  const attempt: CorpusAttempt = {
    id: "ATTEMPT-P", statement_ids: ["STMT-P"], date: "2026-11-04", kind: "reading", outcome: "blocked",
    summary: `Short research context. ${"Extensive argument and evidence. ".repeat(30)}`,
    evidence: ["PR-123"], blocker: "Full blocker details belong on the attempt page",
  };
  const html = renderToStaticMarkup(createElement(DossierAttemptIndex, { attempts: [attempt] }));
  expect(html).toContain('id="ATTEMPT-P"');
  expect(html).toContain('href="/attempts/ATTEMPT-P"');
  expect(html).toContain("blocked");
  expect(html).toContain("Short research context.");
  expect(html).not.toContain("Full blocker details belong on the attempt page");
  expect(html).not.toContain(attempt.summary);
});
