import { afterAll, beforeAll, expect, test } from "bun:test";
import { execFileSync } from "node:child_process";
import path from "node:path";
import { chromium, type Browser } from "playwright";
import type { FrontierReport } from "../src/lib/site-state";
import type { NextStepsReport } from "../src/lib/next-steps";
import { shortId } from "../src/lib/corpus-ids";

let browser: Browser;
let server: ReturnType<typeof Bun.serve> | undefined;
let url: string;
let report: NextStepsReport & { support_options: FrontierReport["support_options"] };
const basePath = process.env.TEST_BASE_PATH ?? "";

beforeAll(async () => {
  report = JSON.parse(execFileSync("python3", ["scripts/corpus.py", "next-steps", "--json"], {
    cwd: path.resolve(import.meta.dir, "../../.."), encoding: "utf8", maxBuffer: 64 * 1024 * 1024,
  }));
  if (process.env.TEST_NEXT_URL) url = process.env.TEST_NEXT_URL;
  else {
    const root = path.resolve(import.meta.dir, "../out");
    server = Bun.serve({ port: 0, async fetch(request) {
      const requested = decodeURIComponent(new URL(request.url).pathname);
      const pathname = basePath && requested.startsWith(`${basePath}/`) ? requested.slice(basePath.length) : requested;
      const relative = pathname.endsWith("/") ? `${pathname}index.html` : pathname;
      const file = path.resolve(root, `.${relative}`);
      if (!file.startsWith(`${root}${path.sep}`)) return new Response("Not found", { status: 404 });
      const artifact = Bun.file(file);
      return await artifact.exists() ? new Response(artifact) : new Response("Not found", { status: 404 });
    }});
    url = `${server.url}${basePath.replace(/^\//, "")}${basePath ? "/" : ""}next/`;
  }
  browser = await chromium.launch({ headless: true });
}, 120000);

afterAll(async () => { await browser?.close(); server?.stop(); });

test("next-work view shares frontier routes, costs, leaves, floor and DAG navigation", async () => {
  const page = await browser.newPage({ viewport: { width: 1440, height: 1000 } });
  const errors: string[] = [];
  page.on("pageerror", (error) => errors.push(error.message));
  await page.goto(url, { timeout: 120000, waitUntil: "domcontentloaded" });
  await page.getByRole("heading", { name: "What to work on next", exact: true }).waitFor();
  const support = page.getByRole("region", { name: "Foundational progress and support options" });
  expect(await support.innerText()).toContain(`${report.progress.verified_alternative_bundle_count} distinct verified premise bundles`);
  await support.getByText(/^Inspect .* premises with verified alternatives$/).click();
  expect(await support.innerText()).toContain("Direct assumption remains available");
  for (const item of report.support_options.items.filter((item) => item.verified_alternative_bundles.length)) {
    const entry = support.locator(":scope > details > ul > li > a")
      .and(support.getByRole("link", { name: item.statement_id, exact: true })).locator("..");
    expect(await entry.innerText()).toContain(item.established ? "Established in the corpus" : "Direct assumption remains available");
    for (const bundle of item.verified_alternative_bundles) {
      for (const id of [...bundle.premise_statement_ids, ...bundle.result_ids]) {
        expect(await entry.getByRole("link", { name: id, exact: true }).count()).toBeGreaterThan(0);
      }
      for (const id of bundle.argument_ids) expect(await entry.innerText()).toContain(id);
    }
  }
  const routes = page.getByRole("heading", { name: "Expanded-route cost (diagnostic)", exact: true }).locator("..").getByRole("row");
  expect(await routes.count()).toBe(report.routes.length + 1);
  expect(await routes.nth(1).innerText()).toContain(report.cheapest_argument_id!);
  expect(await routes.nth(1).innerText()).toContain(String(report.routes.find((route) => route.cheapest)!.cost));
  const leaves = report.leaves.filter((leaf) => leaf.on_cheapest_route);
  for (const leaf of leaves) expect(await page.locator(`[id="leaf-${leaf.statement_id}"]`).count()).toBe(1);
  const first = page.locator(`[id="leaf-${leaves[0].statement_id}"]`);
  expect(await first.innerText()).toContain(`${leaves[0].impact.routes_improved} routes improve`);
  expect(await first.innerText()).toContain("accepting this as floor requires approval");
  expect(await page.locator("#joint-settlements").innerText()).toContain("every failure mode");
  expect(await page.locator("#floor-register").getByRole("link", { name: "Owner approval" }).count()).toBe(report.floor_register.filter((entry) => entry.owner_approval).length);
  const map = page.getByRole("region", { name: "Follow the argument DAG" });
  const chosen = report.dag.arguments.find((argument) => argument.argument_id === report.cheapest_argument_id)!;
  const sid = chosen.premise_statement_ids[0];
  const premise = report.dag.statements.find((statement) => statement.statement_id === sid)!;
  await map.getByRole("button", { name: premise.paraphrase, exact: true }).click();
  expect(await map.innerText()).toContain(shortId(sid));
  await map.getByRole("button", { name: "Return to root", exact: true }).click();
  expect(await map.getByRole("combobox").inputValue()).toBe(report.cheapest_argument_id!);
  expect(errors).toEqual([]);
  await page.setViewportSize({ width: 390, height: 844 });
  expect(await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth + 1)).toBe(true);
  await page.close();
}, 120000);
