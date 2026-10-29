import { expect, test } from "bun:test";

import { getFrontierReport } from "./site-state";
import { sourceAttribution } from "./source-attribution";

test("frontier attribution distinguishes direct claims, support alone, and bare premises", () => {
  const items = getFrontierReport().items;
  const bridge = items.find((item) => item.statement_id === "STMT-CAUSE-OF-BEING-CAUSES-EVERY-PERFECTION")!;
  expect(bridge.stating_claims).toEqual([]);
  expect(bridge.supporting_claims).toHaveLength(2);
  expect(sourceAttribution(bridge)).toContain("No source claim directly attributes this statement");
  const direct = items.find((item) => item.stating_claims.length > 0)!;
  expect(sourceAttribution(direct)).toContain("directly attribute this statement");
  const bare = items.find((item) => !item.stating_claims.length && !item.supporting_claims.length)!;
  expect(sourceAttribution(bare)).toContain("It is bare");
});
