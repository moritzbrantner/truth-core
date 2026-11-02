import { afterAll, beforeAll, expect, test } from "bun:test";
import path from "node:path";
import { chromium, type Browser } from "playwright";

let browser: Browser;
let server: ReturnType<typeof Bun.serve> | undefined;
const root = path.resolve(import.meta.dir, "../out");
const basePath = process.env.TEST_BASE_PATH ?? "";
const testOrigin = process.env.FOREST_TARGET_ORIGIN;

beforeAll(async () => {
  if (!testOrigin) {
    server = Bun.serve({ port: 0, async fetch(request) {
      let pathname = decodeURIComponent(new URL(request.url).pathname);
      if (basePath && pathname.startsWith(basePath + "/")) { pathname = pathname.slice(basePath.length); }
      const file = path.resolve(root, "." + (pathname.endsWith("/") ? pathname + "index.html" : pathname));
      if (!file.startsWith(root + path.sep) || !(await Bun.file(file).exists())) {
        return new Response("Not found", { status: 404 });
      }
      return new Response(Bun.file(file));
    } });
  }
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
  await page.goto(new URL(basePath + "/forest/", testOrigin ?? server!.url).toString());
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

test("single-tree assumptions: all argument routes, deep expansion, scenario selections and mobile", async () => {
  const page = await browser.newPage({ viewport: { width: 1360, height: 900 } });
  const errors: string[] = [];
  page.on("pageerror", (error) => errors.push(error.message));
  const url = new URL(basePath + "/forest/assumptions/", testOrigin ?? server!.url);
  url.searchParams.set("goal", "STMT-CATHOLICISM-TRUE");
  await page.goto(url.toString());
  const tree = page.getByRole("region", { name: "Single proposition tree" });
  const orLabel = tree.getByText(/^OR · \d+ recorded arguments supporting this conclusion$/).first();
  await orLabel.waitFor();
  const total = Number((await orLabel.textContent())?.match(/OR · (\d+)/)?.[1]);
  expect(total).toBeGreaterThan(2);
  expect(await tree.getByRole("region", { name: /^Argument / }).count()).toBe(total);
  expect(await tree.locator("[data-readiness]").count()).toBe(total);
  expect(await tree.getByText("More premises needed").count()).toBeGreaterThan(0);
  await tree.getByText("What-if · unresolved").first().waitFor();

  const deeper = tree.getByRole("button", { name: /^Expand all arguments for / });
  expect(await deeper.count()).toBeGreaterThan(0);
  await deeper.first().click();
  await page.waitForURL((next) => next.searchParams.getAll("open").some((entry) => entry.includes("/")));
  expect(await tree.getByText(/^OR · \d+ recorded argument/).count()).toBeGreaterThan(1);
  await page.reload();
  expect(await tree.getByText(/^OR · \d+ recorded argument/).count()).toBeGreaterThan(1);
  for (let depth = 0; depth < 3; depth += 1) {
    const next = tree.getByRole("button", { name: /^Expand all arguments for / }).first();
    if (!(await next.count())) { break; }
    const before = await tree.getByText(/^OR · \d+ recorded argument/).count();
    await next.click();
    await page.waitForFunction((minimum) => [...document.querySelectorAll("p")]
      .filter((node) => /^OR · \d+ recorded argument/.test(node.textContent ?? "")).length > minimum, before);
  }
  await page.setViewportSize({ width: 390, height: 844 });
  expect(await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth + 1)).toBe(true);
  if (process.env.FOREST_SCREENSHOTS) {
    await page.screenshot({ path: path.join(process.env.FOREST_SCREENSHOTS, "assumptions-deep-mobile.png"), fullPage: true });
  }
  await page.setViewportSize({ width: 1360, height: 900 });

  const rootChoice = tree.getByRole("group", { name: "Hypothetical truth of STMT-CATHOLICISM-TRUE" });
  await rootChoice.getByRole("button", { name: "True" }).click();
  await page.waitForFunction(() => JSON.parse(localStorage.getItem("truth-core:belief-profile:v1") ?? "null")?.accepted.includes("STMT-CATHOLICISM-TRUE"));
  expect(new URL(page.url()).searchParams.has("yes")).toBe(false);
  expect(await rootChoice.getByRole("button", { name: "True" }).getAttribute("aria-pressed")).toBe("true");
  await rootChoice.getByRole("button", { name: "False" }).click();
  await page.getByRole("region", { name: "Review reversing a saved belief" }).getByRole("button", { name: "Withdraw earlier choice and continue" }).click();
  await page.waitForFunction(() => {
    const belief = JSON.parse(localStorage.getItem("truth-core:belief-profile:v1") ?? "null");
    return belief?.denied.includes("STMT-CATHOLICISM-TRUE") && !belief.accepted.includes("STMT-CATHOLICISM-TRUE");
  });
  await page.reload();
  expect(await rootChoice.getByRole("button", { name: "False" }).getAttribute("aria-pressed")).toBe("true");
  await page.getByRole("button", { name: "Copy scenario link" }).click();
  const shared = new URL(await page.getByLabel("Shareable preview URL (select to copy)").inputValue());
  expect(shared.searchParams.get("preview")).toBe("1");
  expect(shared.searchParams.getAll("no")).toContain("STMT-CATHOLICISM-TRUE");
  shared.searchParams.delete("no");
  shared.searchParams.append("yes", "STMT-CATHOLICISM-TRUE");
  await page.goto(shared.toString());
  await page.getByText("Shared what-if preview · not saved").waitFor();
  expect(await rootChoice.getByRole("button", { name: "True" }).getAttribute("aria-pressed")).toBe("true");
  expect(await page.evaluate(() => JSON.parse(localStorage.getItem("truth-core:belief-profile:v1") ?? "null")?.denied))
    .toContain("STMT-CATHOLICISM-TRUE");
  await page.getByRole("button", { name: "Return to saved beliefs" }).click();
  await page.waitForURL((next) => !next.searchParams.has("preview") && !next.searchParams.has("yes"));
  expect(await rootChoice.getByRole("button", { name: "False" }).getAttribute("aria-pressed")).toBe("true");
  await page.getByLabel("Find a proposition to investigate or assume").fill("STMT-NECESSARY-CLASSICAL-GOD-ROOT");
  const searchResults = page.getByRole("list", { name: "Matching propositions" });
  expect(await searchResults.getByRole("button").first().getByText("STMT-NECESSARY-CLASSICAL-GOD-ROOT", { exact: true }).count()).toBe(1);
  await searchResults.getByText("STMT-NECESSARY-CLASSICAL-GOD-ROOT", { exact: true }).click();
  await page.waitForURL((next) => next.searchParams.get("goal") === "STMT-NECESSARY-CLASSICAL-GOD-ROOT");
  if (process.env.FOREST_SCREENSHOTS) {
    await page.screenshot({ path: path.join(process.env.FOREST_SCREENSHOTS, "assumptions-desktop.png"), fullPage: true });
  }
  await page.setViewportSize({ width: 390, height: 844 });
  expect(await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth + 1)).toBe(true);
  if (process.env.FOREST_SCREENSHOTS) {
    await page.screenshot({ path: path.join(process.env.FOREST_SCREENSHOTS, "assumptions-mobile.png"), fullPage: true });
  }
  expect(errors).toEqual([]);
  await page.close();
}, 90000);

test("assumption explorer: mobile touch can expand, select and revisit a proposition", async () => {
  const context = await browser.newContext({ viewport: { width: 390, height: 844 }, isMobile: true, hasTouch: true });
  const page = await context.newPage();
  await page.goto(new URL(basePath + "/forest/assumptions/", testOrigin ?? server!.url).toString());
  const tree = page.getByRole("region", { name: "Single proposition tree" });
  await tree.getByRole("button", { name: /^Expand all arguments for / }).first().tap();
  await tree.getByText(/^OR · \d+ recorded argument/).first().waitFor();
  const belief = tree.getByRole("group", { name: /^Hypothetical truth of / }).first();
  await belief.getByRole("button", { name: "True" }).tap();
  await page.waitForFunction(() => JSON.parse(localStorage.getItem("truth-core:belief-profile:v1") ?? "null")?.accepted.length > 0);
  expect(await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth + 1)).toBe(true);
  await page.reload();
  const restoredTrue = belief.getByRole("button", { name: "True" });
  await restoredTrue.and(page.locator('[aria-pressed="true"]')).waitFor();
  expect(await restoredTrue.getAttribute("aria-pressed")).toBe("true");
  await context.close();
}, 90000);

test("network markers render only their custom label, without a native title tooltip", async () => {
  const page = await browser.newPage({ viewport: { width: 1300, height: 900 } });
  await page.goto(new URL(basePath + "/graph/", testOrigin ?? server!.url).toString());
  const marker = page.locator(".network-marker").first();
  await marker.waitFor();
  expect(await marker.getAttribute("title")).toBeNull();
  expect(await marker.locator(".network-label").count()).toBe(1);
  await page.close();
}, 60000);
