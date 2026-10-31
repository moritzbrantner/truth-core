import { afterAll, beforeAll, expect, test } from "bun:test";
import path from "node:path";
import { chromium, type Browser } from "playwright";

let browser: Browser;
let server: ReturnType<typeof Bun.serve>;
const root = path.resolve(import.meta.dir, "../out");
const basePath = process.env.TEST_BASE_PATH ?? "";

beforeAll(async () => {
  server = Bun.serve({ port: 0, async fetch(request) {
    let pathname = decodeURIComponent(new URL(request.url).pathname);
    if (basePath && pathname.startsWith(basePath + "/")) { pathname = pathname.slice(basePath.length); }
    const file = path.resolve(root, "." + (pathname.endsWith("/") ? pathname + "index.html" : pathname));
    if (!file.startsWith(root + path.sep) || !(await Bun.file(file).exists())) {
      return new Response("Not found", { status: 404 });
    }
    return new Response(Bun.file(file));
  } });
  browser = await chromium.launch({ headless: true });
}, 30000);

afterAll(async () => {
  await browser?.close();
  server?.stop();
});

test("argument forest: real conclusion routes, comparison, hypothetical reversal and mobile", async () => {
  const page = await browser.newPage({ viewport: { width: 1360, height: 900 } });
  const errors: string[] = [];
  page.on("pageerror", (error) => errors.push(error.message));
  await page.goto(new URL(basePath + "/forest/", server.url).toString());
  await page.getByRole("heading", { name: "Argument forest", exact: true }).waitFor();
  const primary = page.getByRole("region", { name: "Primary conclusion" });
  const comparison = page.getByRole("region", { name: "Compared conclusion" });
  await primary.getByRole("button", { name: /^Select proposition:/ }).first().waitFor();
  expect(await comparison.getByRole("button", { name: /^Select proposition:/ }).count()).toBeGreaterThan(0);
  expect(await primary.getByText(/^OR ·/).count()).toBeGreaterThan(0);

  const premise = primary.getByRole("button", { name: /^Select proposition:/ }).last();
  await premise.click();
  await page.waitForURL((url) => url.searchParams.has("sel"));
  await page.getByRole("button", { name: "Explore ¬P" }).click();
  await page.waitForURL((url) => url.searchParams.get("flip") === "1");
  await page.getByRole("region", { name: "Hypothetical negation" }).waitFor();
  await page.getByText(/Losing an argument does not prove its conclusion false/).waitFor();
  await page.reload();
  await page.getByRole("region", { name: "Hypothetical negation" }).waitFor();
  await page.getByRole("button", { name: "Return to comparison" }).click();
  await page.getByRole("region", { name: "Compared conclusion" }).waitFor();

  const choices = page.getByLabel("Compare against");
  expect(await choices.locator("option").count()).toBeGreaterThan(0);
  const last = await choices.locator("option").last().getAttribute("value");
  if (last) {
    await choices.selectOption(last);
    await page.waitForURL((url) => url.searchParams.get("compare") === last);
  }
  if (process.env.FOREST_SCREENSHOTS) {
    await page.screenshot({ path: path.join(process.env.FOREST_SCREENSHOTS, "forest-desktop.png"), fullPage: true });
  }
  await page.setViewportSize({ width: 390, height: 844 });
  expect(await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth + 1)).toBe(true);
  if (process.env.FOREST_SCREENSHOTS) {
    await page.screenshot({ path: path.join(process.env.FOREST_SCREENSHOTS, "forest-mobile.png"), fullPage: true });
  }
  expect(errors).toEqual([]);
  await page.close();
}, 90000);

test("network markers render only their custom label, without a native title tooltip", async () => {
  const page = await browser.newPage({ viewport: { width: 1300, height: 900 } });
  await page.goto(new URL(basePath + "/graph/", server.url).toString());
  const marker = page.locator(".network-marker").first();
  await marker.waitFor();
  expect(await marker.getAttribute("title")).toBeNull();
  expect(await marker.locator(".network-label").count()).toBe(1);
  await page.close();
}, 60000);
