import { expect, test } from "bun:test";
import { createElement } from "react";
import { renderToStaticMarkup } from "react-dom/server";

import type { Terms } from "@/lib/corpus";

import { DossierTermIndex } from "./dossier-term-index";

test("dossier term index retains canonical links and local anchors without copying full texts", () => {
  const terms: Terms = {
    definitions: [{ id: "DEF-CAUSE-A", term: "Cause", basis: "sourced", definition: "Full definition text", claim_ids: ["CLAIM-A"] }],
    disambiguations: [{ id: "DISAMB-CAUSE", term: "Cause", sense_definition_ids: ["DEF-CAUSE-A"], resolution: "Full resolution text" }],
  };

  const html = renderToStaticMarkup(createElement(DossierTermIndex, { terms }));
  expect(html).toContain('href="/definitions/DEF-CAUSE-A"');
  expect(html).toContain('href="/definitions#DISAMB-CAUSE"');
  expect(html).toContain('id="DISAMB-CAUSE"');
  expect(html).toContain("(sourced)");
  expect(html).not.toContain("Full definition text");
  expect(html).not.toContain("Full resolution text");
});
