import { afterAll, beforeAll, expect, test } from "bun:test";
import path from "node:path";
import { chromium, type Browser } from "playwright";


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

test("fork use leads from consumed inference to coverage theorem and back to its consequence", async () => {
  const page = await browser.newPage({ viewport: { width: 1280, height: 900 } });
  const errors: string[] = [];
  page.on("pageerror", (error) => errors.push(error.message));
  const base = `${server.url}${basePath.replace(/^\//, "")}${basePath ? "/" : ""}`;
  await page.goto(`${base}results/RECIPROCAL-EVENT-RESPECT-CONSTRAINT/`);
  const marker = page.getByRole("region", { name: "Fork applied here", exact: true });
  await marker.waitFor();
  expect(await marker.innerText()).toContain("INF-TEMPORAL-RECIPROCAL-FORK-USE");
  expect(await marker.innerText()).toContain("simultaneous alternating circle");
  expect(await marker.innerText()).toContain("All six advertised premises remain");
  const coverage = marker.getByRole("link", { name: "TEMPORAL-DIRECTION-FRAMEWORK", exact: true });
  expect(await coverage.getAttribute("href")).toBe(`${basePath}/results/TEMPORAL-DIRECTION-FRAMEWORK/`);
  await coverage.click();
  await page.waitForURL((url) => url.pathname.endsWith("/results/TEMPORAL-DIRECTION-FRAMEWORK/"));
  expect(await page.getByRole("heading", { level: 1 }).innerText()).toContain("linearly ordered time carrier");
  expect(await page.locator(".lean-snippet").innerText()).toContain("theorem framework");
  expect(await page.locator("article").innerText()).toContain("pairwise incompatibility");
  await page.goBack();
  await marker.waitFor();
  await marker.getByRole("link", { name: "STMT-RECIPROCAL-EVENT-RESPECT-CONSTRAINT", exact: true }).click();
  await page.waitForURL((url) => url.pathname.endsWith("/statements/STMT-RECIPROCAL-EVENT-RESPECT-CONSTRAINT/"));
  expect(await page.getByRole("heading", { level: 1 }).innerText()).toContain("distinct target event respects");
  await page.goBack();
  await marker.waitFor();
  await page.setViewportSize({ width: 390, height: 844 });
  expect(await marker.evaluate((element) => element.scrollWidth <= element.clientWidth + 1 && element.getBoundingClientRect().right <= window.innerWidth + 1)).toBe(true);
  expect(errors).toEqual([]);
  await page.close();
}, 60000);
