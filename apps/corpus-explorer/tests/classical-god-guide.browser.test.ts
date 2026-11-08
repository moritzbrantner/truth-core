import { afterAll, beforeAll, expect, test } from "bun:test";
import path from "node:path";
import { chromium, type Browser } from "playwright";
import { uid } from "./corpus-records";

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

test("classical-God guide links exact evidence, navigates all stages, and fits mobile", async () => {
  const page = await browser.newPage({ viewport: { width: 1360, height: 900 } });
  const errors: string[] = [];
  page.on("pageerror", (error) => errors.push(error.message));
  await page.goto(new URL(basePath + "/guide/classical-god/", server.url).toString());
  await page.getByRole("heading", { name: "From a necessary being to a classical-God conclusion" }).waitFor();
  expect(await page.locator("section[id^='step-']").count()).toBe(3);
  await page.getByText(/Conditional conclusion, not an unconditional proof of God/).waitFor();
  await page.getByText(/Fewest open leaves on any route/).waitFor();

  await page.getByRole("navigation", { name: "Walkthrough steps" }).getByRole("link", { name: /The conditional classical-God conclusion/ }).click();
  await page.waitForURL((url) => url.hash === "#step-3");
  const finalStep = page.locator("#step-3");
  await finalStep.getByRole("heading", { name: "The conditional classical-God conclusion" }).waitFor();
  const evidence = finalStep.locator("details").first();
  await evidence.getByText(/all 11 named inputs/).click();
  expect(await evidence.locator("ol li").count()).toBe(11);
  expect(await finalStep.getByRole("link", { name: "Lean solution ↗" }).getAttribute("href"))
    .toContain("ClassicalGodFromPositiveRoot/Solution.lean");
  expect(await finalStep.getByRole("link", { name: "Source, rivals and countermodel status" }).count()).toBe(3);
  await page.reload();
  await page.locator("#step-3").waitFor();

  if (process.env.GUIDE_SCREENSHOTS) {
    await page.screenshot({ path: path.join(process.env.GUIDE_SCREENSHOTS, "classical-god-desktop.png"), fullPage: true });
  }
  await page.setViewportSize({ width: 390, height: 844 });
  expect(await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth + 1)).toBe(true);
  if (process.env.GUIDE_SCREENSHOTS) {
    await page.screenshot({ path: path.join(process.env.GUIDE_SCREENSHOTS, "classical-god-mobile.png"), fullPage: true });
  }

  await page.getByRole("link", { name: /Explore this conclusion in the argument forest/ }).click();
  await page.waitForURL((url) => url.pathname.endsWith("/forest/") &&
    url.searchParams.get("goal") === uid("statement", "STMT-NECESSARY-CLASSICAL-GOD-ROOT"));
  expect(await page.getByLabel("Conclusion to investigate").inputValue()).toBe(uid("statement", "STMT-NECESSARY-CLASSICAL-GOD-ROOT"));
  expect(errors).toEqual([]);
  await page.close();
}, 90000);
