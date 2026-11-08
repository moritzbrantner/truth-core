import { expect, test } from "bun:test";
import { auditRecordHref, getBundleAudit } from "./bundle-audit";
import { legacyUuid } from "./corpus-ids";

test("bounded audit exposes exact coverage and keeps unrelated results outside scope", () => {
  const audit = getBundleAudit(legacyUuid("result", "CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES"));
  expect(audit?.records.length).toBe(69);
  expect(audit?.records.filter((r) => r.kind === "definitions").length).toBe(25);
  expect(audit?.records.find((r) => r.id === legacyUuid("statement", "STMT-CAUSE-OF-QUALITY-IN-ANOTHER-IS-MORE-SUCH"))?.status).toBe("unresolved");
  expect(audit?.limits.join(" ")).toContain("#720");
  const complete = getBundleAudit(legacyUuid("result", "CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES-ALL"));
  expect(complete?.records.length).toBe(151);
  expect(complete?.records.some((r) => r.kind === "definitions" && r.id === legacyUuid("definition", "DEF-INDEPENDENT-POTENCY"))).toBe(true);
  expect(complete?.records.some((r) => r.kind === "disambiguations" && r.id === legacyUuid("disambiguation", "DISAMB-POTENCY"))).toBe(true);
  expect(getBundleAudit(legacyUuid("result", "CATHOLICISM-STAGES-ONE-TWO-Q11-NATURE"))).toBe(complete);
  expect(getBundleAudit(legacyUuid("result", "CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES-IDENTITY"))).toBe(complete);
  expect(getBundleAudit(legacyUuid("result", "CATHOLICISM-SKELETON"))).toBeUndefined();
  const excludedMiddle = legacyUuid("statement", "STMT-EXCLUDED-MIDDLE");
  expect(auditRecordHref("statements", excludedMiddle)).toBe(`/statements/${excludedMiddle}`);
  expect(auditRecordHref("inferences", legacyUuid("inference", "INF-STAGE2-CLASSICAL-ATTRIBUTES"))).toBeUndefined();
}, 60000);
