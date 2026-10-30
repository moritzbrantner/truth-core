import { expect, test } from "bun:test";

import { getDossiers } from "./premise-dossier";
import { getFrontierReport } from "./site-state";
import { sourceAttribution } from "./source-attribution";

test("source attribution distinguishes direct claims, support alone, and bare premises independently of closure", () => {
  const items = getFrontierReport().items;
  // Conditional reconstruction can remove this target from frontier.items
  // while its source support remains unchanged. The dossier owns attribution
  // independently of whether the statement is an open item or a derived one.
  const dossier = getDossiers()["STMT-CAUSE-OF-BEING-CAUSES-EVERY-PERFECTION"];
  const bridge = { stating_claims: dossier.claim_ids, supporting_claims: dossier.supporting_claim_ids };
  expect(bridge.stating_claims).toEqual([]);
  expect(bridge.supporting_claims).toHaveLength(2);
  expect(sourceAttribution(bridge)).toContain("No source claim directly attributes this statement");
  const direct = items.find((item) => item.stating_claims.length > 0)!;
  expect(sourceAttribution(direct)).toContain("directly attribute this statement");
  const bare = items.find((item) => !item.stating_claims.length && !item.supporting_claims.length)!;
  expect(sourceAttribution(bare)).toContain("It is bare");
});
