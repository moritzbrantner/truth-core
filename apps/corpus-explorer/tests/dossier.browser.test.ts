import { afterAll, beforeAll, expect, test } from "bun:test";
import path from "node:path";
import { chromium, type Browser } from "playwright";

import { getDossiers } from "../src/lib/premise-dossier";

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
  await page.goto(`${base}statements/STMT-ACT-SIMPLY-PRIOR-TO-POTENCY/`);
  await page.getByRole("link", { name: "Premise dossier and attempt log →", exact: true }).click();
  await page.waitForURL((url) => url.pathname.endsWith("/dossiers/STMT-ACT-SIMPLY-PRIOR-TO-POTENCY/"));
  await page.getByRole("heading", { name: "Premise dossier", exact: true }).waitFor();
  expect(await page.getByRole("region", { name: "Current status", exact: true }).innerText()).toContain("not established");
  const attempts = page.getByRole("region", { name: "Attempt log", exact: true });
  expect(await attempts.innerText()).toContain("Finite omission models");
  expect(await attempts.getByRole("link", { name: "PR-374", exact: true }).getAttribute("href")).toBe("https://github.com/moritzbrantner/truth-core/pull/374");
  const originalAttempt = attempts.locator("#ATTEMPT-ACT-POTENCY-INDEPENDENCE");
  expect(await originalAttempt.getByRole("link", { name: "ACT-POTENCY-PREMISES-INDEPENDENT", exact: true }).getAttribute("href")).toBe(`${basePath}/results/ACT-POTENCY-PREMISES-INDEPENDENT/`);
  const models = page.getByRole("region", { name: "Schema instances and countermodels", exact: true });
  const registration = models.getByRole("listitem").filter({ hasText: "MODEL-ACT-POTENCY-M3" });
  expect(await registration.innerText()).toContain("violates");
  await registration.getByText("Statement application and certificate", { exact: true }).click();
  expect(await registration.innerText()).toContain("TruthCore.Models.ActPotency.M3.evaluation9");
  const routes = page.getByRole("table", { name: "Open-leaf contribution to routes concluding STMT-CATHOLICISM-TRUE", exact: true });
  // A new route to the root adds a row; the expectation follows the emitted dossier (#520).
  const routeCount = getDossiers()["STMT-ACT-SIMPLY-PRIOR-TO-POTENCY"].route_contributions.length;
  expect(routeCount).toBeGreaterThan(0);
  expect(await routes.locator("tbody tr").count()).toBe(routeCount);
  await page.reload();
  await page.getByRole("heading", { name: "Attempt log", exact: true }).waitFor();
  await page.setViewportSize({ width: 390, height: 844 });
  expect(await page.locator("article").evaluate((element) => element.scrollWidth <= element.clientWidth + 1 && element.getBoundingClientRect().right <= window.innerWidth + 1)).toBe(true);
  await page.close();
}, 60000);
