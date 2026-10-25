import { afterAll, beforeAll, expect, test } from "bun:test";
import path from "node:path";
import { chromium, type Browser } from "playwright";

import { getCorpus } from "../src/lib/corpus";
import { getPropositionGraph } from "../src/lib/proposition-graph-data";
import { researchFrontier } from "../src/lib/research-frontier";
import { getFrontierReport } from "../src/lib/site-state";
import { skeletonProgress } from "../src/app/skeleton/progress";

let browser: Browser;
let server: ReturnType<typeof Bun.serve>;
const root = path.resolve(import.meta.dir, "../out");
const basePath = process.env.TEST_BASE_PATH ?? "";
const corpus = getCorpus();
const report = getFrontierReport();
const progress = skeletonProgress(corpus, report, researchFrontier(corpus, getPropositionGraph(corpus), report));

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
      return await artifact.exists() ? new Response(artifact) : new Response("Not found", { status: 404 });
    },
  });
  browser = await chromium.launch({ headless: true });
}, 30000);

afterAll(async () => {
  await browser?.close();
  server?.stop();
});

test("skeleton: route, conditional versus discharged, next gap, proof links, reload and mobile", async () => {
  const page = await browser.newPage({ viewport: { width: 1440, height: 1000 } });
  const errors: string[] = [];
  page.on("pageerror", (error) => errors.push(error.message));
  const url = new URL(`${basePath}/skeleton/`, server.url).toString();
  await page.goto(url);
  await page.getByRole("heading", { name: "Skeleton progress", exact: true }).waitFor();
  expect(await page.getByText(`${progress.obligations.length} open premises`, { exact: false }).count()).toBeGreaterThan(0);
  expect(await page.getByText("Root not discharged.", { exact: false }).count()).toBe(1);
  const connections = page.getByRole("region", { name: "Checked connections" });
  expect(await connections.getByText("Connected · conditional proof", { exact: true }).count()).toBeGreaterThan(0);
  expect(await connections.getByText("Discharged · established", { exact: true }).count()).toBeGreaterThan(0);
  const rootRoute = connections.locator("details").first();
  await rootRoute.locator("summary").click();
  expect(await rootRoute.getByRole("link", { name: progress.routes[0].argument.id, exact: true }).count()).toBe(1);
  expect(await rootRoute.getByRole("link", { name: "CATHOLICISM-FROM-PRIMA-VIA-WITH-Q11-UNIQUENESS", exact: true }).count()).toBe(0);

  // Exact theorem provenance remains inspectable even when the conclusion is conditional.
  const witnessStep = connections.locator("ol > li").filter({ hasText: "CATHOLICISM-STAGES-ONE-TWO-SAME-WITNESS" }).first();
  await witnessStep.locator("summary").click();
  await witnessStep.getByRole("link", { name: "CATHOLICISM-STAGES-ONE-TWO-SAME-WITNESS", exact: true }).click();
  await page.waitForURL((value) => value.pathname === `${basePath}/results/CATHOLICISM-STAGES-ONE-TWO-SAME-WITNESS/`);
  await page.getByRole("heading", { name: "The advertised theorem", exact: true }).waitFor();
  await page.goto(url);

  const obligations = page.getByRole("region", { name: "Root obligations" });
  expect(await obligations.locator("ol > li").count()).toBe(progress.obligations.length);
  const gap = progress.obligations.find((entry) => entry.candidates.length > 0)!;
  const gapPanel = page.locator(`#obligation-${gap.item.statement_id}`);
  await gapPanel.locator("summary").click();
  await gapPanel.getByRole("heading", { name: "Next recorded gap", exact: true }).waitFor();
  expect(await gapPanel.getByRole("link", { name: "Read queued source and interpretation notes", exact: true }).count()).toBe(gap.candidates.length);
  expect(await gapPanel.getByText("Discharged · established", { exact: true }).count()).toBe(0);
  const unrecorded = progress.obligations.find((entry) => entry.candidates.length === 0)!;
  const unrecordedPanel = page.locator(`#obligation-${unrecorded.item.statement_id}`);
  await unrecordedPanel.locator("summary").click();
  await unrecordedPanel.getByRole("heading", { name: "Next inference not recorded", exact: true }).waitFor();
  await page.screenshot({ path: `/tmp/skeleton-progress${basePath ? "-pages" : ""}-desktop.png`, fullPage: true });
  await gapPanel.getByRole("link", { name: "Explore missing inference", exact: true }).click();
  await page.waitForURL((value) => value.pathname === `${basePath}/graph/` && value.searchParams.get("target") === gap.item.statement_id);
  await page.getByRole("region", { name: "Proof exploration results" }).waitFor();
  await page.reload();
  expect(new URL(page.url()).searchParams.get("explore")).toBe("1");

  await page.setViewportSize({ width: 390, height: 844 });
  await page.goto(url);
  await page.getByRole("heading", { name: "Skeleton progress", exact: true }).waitFor();
  await page.locator(`#obligation-${gap.item.statement_id} summary`).click();
  await page.screenshot({ path: `/tmp/skeleton-progress${basePath ? "-pages" : ""}-mobile.png`, fullPage: true });
  expect(await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth + 1)).toBe(true);
  await page.evaluate(() => window.scrollTo(0, 0));
  await page.screenshot({ path: `/tmp/skeleton-progress${basePath ? "-pages" : ""}-mobile-viewport.png` });
  expect(errors).toEqual([]);
  await page.close();
}, 60000);
