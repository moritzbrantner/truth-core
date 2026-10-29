import { expect, test } from "bun:test";
import { auditRecordHref, getBundleAudit } from "./bundle-audit";

test("bounded audit exposes exact coverage and keeps unrelated results outside scope", () => {
  const audit = getBundleAudit("CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES");
  expect(audit?.records.length).toBe(69);
  expect(audit?.records.filter((r) => r.kind === "definitions").length).toBe(25);
  expect(audit?.records.find((r) => r.id === "STMT-CAUSE-OF-QUALITY-IN-ANOTHER-IS-MORE-SUCH")?.status).toBe("unresolved");
  expect(audit?.limits.join(" ")).toContain("#720");
  expect(getBundleAudit("CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES-ALL")).toBeUndefined();
  expect(auditRecordHref("statements", "STMT-EXCLUDED-MIDDLE")).toBe("/statements/STMT-EXCLUDED-MIDDLE");
  expect(auditRecordHref("inferences", "INF-STAGE2-CLASSICAL-ATTRIBUTES")).toBeUndefined();
});
