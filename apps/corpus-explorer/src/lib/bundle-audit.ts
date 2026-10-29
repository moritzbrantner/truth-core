import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import path from "node:path";

export type BundleAudit = {
  consumer_result_ids?: string[];
  title: string; result_id: string; base_head: string; root: string;
  designated_route: string; premise_delta: string; limits: string[]; next_scope: string;
  records: Array<{
    kind: string; id: string; path: string; status: string; classification: string; finding: string;
    before: { sha256: string }; reviewed_sha256: string;
  }>;
};

let audits: BundleAudit[] | undefined;
/** Reviewed research note. No proof verdict or frontier state is assigned here. */
export function getBundleAudit(resultId: string): BundleAudit | undefined {
  if (!audits) {
    const root = path.resolve(process.cwd(), "../..");
    execFileSync("python3", ["scripts/bundle_audit.py"], { cwd: root, stdio: "pipe", timeout: 60000 });
    audits = ["classical-attributes-migration.json", "classical-attributes-all-migration.json"].map((file) =>
      JSON.parse(readFileSync(path.join(root, "docs/notes", file), "utf8")));
  }
  return audits.find((audit) => audit.result_id === resultId || audit.consumer_result_ids?.includes(resultId));
}

export function auditRecordHref(kind: string, id: string): string | undefined {
  if (kind === "statements") return `/statements/${id}`;
  if (kind === "results") return `/results/${id}`;
  if (kind === "definitions") return `/definitions/${id}`;
  if (kind === "disambiguations") return `/definitions#${id}`;
  if (kind === "claims") return `/claims/${id}`;
}
