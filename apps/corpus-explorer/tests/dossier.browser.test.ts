import { afterAll, beforeAll, expect, test } from "bun:test";
import path from "node:path";
import { chromium, type Browser } from "playwright";

import { getDossiers } from "../src/lib/premise-dossier";
import { label, uid } from "./corpus-records";

const premise = uid("statement", "STMT-ACT-SIMPLY-PRIOR-TO-POTENCY");
const attempt = uid("attempt", "ATTEMPT-ACT-POTENCY-INDEPENDENCE");

let browser: Browser;
let server: ReturnType<typeof Bun.serve>;
const root = path.resolve(import.meta.dir, "../out");
const basePath = process.env.TEST_BASE_PATH ?? "";

beforeAll(async () => {
  server = Bun.serve({
    port: 0,
    async fetch(request) {
      const requested = decodeURIComponent(new URL(request.url).pathname);
      const pathname = basePath && requested.startsWith(`${basePath}/`) ? requested.slice(basePath.length) : requested;
      const relative = pathname.endsWith("/") ? `${pathname}index.html` : pathname;
      const file = path.resolve(root, `.${relative}`);
      if (!file.startsWith(`${root}${path.sep}`)) {
        return new Response("Not found", { status: 404 });
      }
      const artifact = Bun.file(file);
      if (!(await artifact.exists())) {
        return new Response("Not found", { status: 404 });
      }
      return new Response(artifact);
    },
  });
  browser = await chromium.launch({ headless: true });
}, 30000);

afterAll(async () => {
  await browser?.close();
  server?.stop();
});

test("premise dossier: statement navigation, durable attempt evidence and route contributions", async () => {
  const page = await browser.newPage({ viewport: { width: 1280, height: 900 } });
  const base = `${server.url}${basePath.replace(/^\//, "")}${basePath ? "/" : ""}`;
  await page.goto(`${base}statements/${premise}/`);
  await page.getByRole("link", { name: "Research progress, senses, rivals and attempt log →", exact: true }).click();
  await page.waitForURL((url) => url.pathname.endsWith(`/dossiers/${premise}/`) && url.hash === "#research-comparison");
  await page.getByRole("heading", { name: "Premise dossier", exact: true }).waitFor();
  expect(await page.getByRole("region", { name: "Current status", exact: true }).innerText()).toContain("not established");
  const attempts = page.getByRole("region", { name: "Attempt log", exact: true });
  const originalAttempt = attempts.locator(`[id="${attempt}"]`);
  await originalAttempt.getByRole("link", { name: /Full attempt and evidence/ }).click();
  await page.waitForURL((url) => url.pathname.endsWith(`/attempts/${attempt}/`));
  expect(await page.getByRole("region", { name: "Findings and limits", exact: true }).innerText()).toContain("Finite omission models");
  const evidence = page.getByRole("region", { name: "Evidence", exact: true });
  expect(await evidence.getByRole("link", { name: "PR-374", exact: true }).getAttribute("href")).toBe("https://github.com/moritzbrantner/truth-core/pull/374");
  expect(await evidence.getByRole("link", { name: label("result", "ACT-POTENCY-PREMISES-INDEPENDENT"), exact: true }).getAttribute("href")).toBe(`${basePath}/results/${uid("result", "ACT-POTENCY-PREMISES-INDEPENDENT")}/`);
  await page.getByRole("region", { name: "Related propositions", exact: true }).getByRole("link", { name: `${label("statement", "STMT-ACT-SIMPLY-PRIOR-TO-POTENCY")} · Dossier →`, exact: true }).click();
  await page.waitForURL((url) => url.pathname.endsWith(`/dossiers/${premise}/`) && url.hash === `#${attempt}`);
  const models = page.getByRole("region", { name: "Schema instances and countermodels", exact: true });
  const registration = models.getByRole("listitem").filter({ hasText: label("model", "MODEL-ACT-POTENCY-M3") });
  expect(await registration.innerText()).toContain("violates");
  await registration.getByText("Statement application and certificate", { exact: true }).click();
  expect(await registration.innerText()).toContain("TruthCore.Models.ActPotency.M3.evaluation9");
  const routes = page.getByRole("table", { name: `Open-leaf contribution to routes concluding ${label("statement", "STMT-CATHOLICISM-TRUE")}`, exact: true });
  // A new route to the root adds a row; the expectation follows the emitted dossier (#520).
  const routeCount = getDossiers()[premise].route_contributions.length;
  expect(routeCount).toBeGreaterThan(0);
  expect(await routes.locator("tbody tr").count()).toBe(routeCount);
  await page.reload();
  await page.getByRole("heading", { name: "Attempt log", exact: true }).waitFor();
  await page.setViewportSize({ width: 390, height: 844 });
  expect(await page.locator("article").evaluate((element) => element.scrollWidth <= element.clientWidth + 1 && element.getBoundingClientRect().right <= window.innerWidth + 1)).toBe(true);
  await page.close();
}, 60000);
