import { afterAll, beforeAll, expect, test } from "bun:test";
import path from "node:path";
import { chromium, type Browser } from "playwright";

let browser: Browser;
let server: ReturnType<typeof Bun.serve>;
const root = path.resolve(import.meta.dir, "../out");
const basePath = process.env.TEST_BASE_PATH ?? "";

beforeAll(async () => {
  server = Bun.serve({ port: 0, async fetch(request) {
    const requested = decodeURIComponent(new URL(request.url).pathname);
    const pathname = basePath && requested.startsWith(`${basePath}/`) ? requested.slice(basePath.length) : requested;
    const file = path.resolve(root, `.${pathname.endsWith("/") ? `${pathname}index.html` : pathname}`);
    if (!file.startsWith(`${root}${path.sep}`)) return new Response("Not found", { status: 404 });
    const artifact = Bun.file(file);
    return await artifact.exists() ? new Response(artifact) : new Response("Not found", { status: 404 });
  } });
  browser = await chromium.launch({ headless: true });
}, 30000);
afterAll(async () => { await browser?.close(); server?.stop(); });

test("certified comparisons preserve selected backgrounds, all obligations and separating evidence", async () => {
  const page = await browser.newPage({ viewport: { width: 1280, height: 1050 } });
  const errors: string[] = [];
  page.on("pageerror", (error) => errors.push(error.message));
  const base = `${server.url}${basePath.replace(/^\//, "")}${basePath ? "/" : ""}`;
  await page.goto(`${base}statements/STMT-CAUSE-PRINCIPLE-DISTINCT/#strength-comparisons`);
  const region = page.getByRole("region", { name: "Certified strength comparisons", exact: true });
  const cause = region.locator("[data-strength-comparison]").first();
  expect(await cause.locator("[data-strength-status]").textContent()).toBe("strict strengthening");
  expect(await cause.getByLabel("Selected background").textContent()).toContain("Background Γ");
  expect(await cause.getByLabel("Exact comparison formulas").innerText()).toContain("STMT-CAUSE-PRINCIPLE-BROAD");
  expect(await cause.locator("[data-delta-status]").innerText()).toContain("exact additional requirement proved");
  for (const role of ["implication", "delta_forward", "reconstruction", "equivalence"]) {
    expect(await cause.locator(`[data-strength-role="${role}"]`).innerText()).toContain("proved");
  }
  expect(await cause.locator("[data-strength-separator]").textContent()).toContain("Γ with W ∧ ¬ S");
  expect(await cause.locator("[data-converse-status]").innerText()).toContain("refuted by separating setting");
  const parameters = cause.getByLabel("Comparison parameters and definitions");
  await parameters.locator(":scope > summary").click();
  expect(await parameters.innerText()).toContain("G : Entity → Prop");
  expect(await parameters.innerText()).toContain("C : Entity → Entity → Prop");
  expect(await parameters.innerText()).toContain("DecidableEq Entity");
  const binding = cause.locator('[data-strength-role="implication"] details');
  await binding.locator(":scope > summary").click();
  expect(await binding.innerText()).toContain("Expected type");
  expect(await binding.innerText()).toContain("Bound theorem type");
  await parameters.locator(":scope > summary").click();
  await binding.locator(":scope > summary").click();
  if (process.env.TEST_SCREENSHOT_PATH) {
    await cause.scrollIntoViewIfNeeded();
    const top = await cause.evaluate((element) => element.getBoundingClientRect().top + window.scrollY);
    await page.evaluate((y) => window.scrollTo(0, y), top);
    await page.screenshot({ path: process.env.TEST_SCREENSHOT_PATH });
  }
  await page.setViewportSize({ width: 390, height: 844 });
  expect(await cause.evaluate((element) => element.getBoundingClientRect().right <= window.innerWidth + 1)).toBe(true);
  expect(await cause.evaluate((element) => element.scrollWidth <= element.clientWidth + 1)).toBe(true);
  await page.setViewportSize({ width: 1280, height: 1050 });
  const proof = cause.locator('[data-strength-role="implication"] a').first();
  await proof.click();
  await page.waitForURL("**/results/**");
  expect(page.url()).toContain("/results/");
  expect(await page.getByRole("region", { name: "Certified strength comparisons", exact: true }).count()).toBe(1);
  await page.goto(`${base}comparisons/`);
  const all = page.locator("[data-strength-comparison]");
  expect(await all.count()).toBeGreaterThanOrEqual(3);
  expect(await page.locator('[data-strength-role="allowed_cases"]').count()).toBeGreaterThanOrEqual(1);
  expect(await page.locator('[data-strength-role="remainder_identity"]').count()).toBeGreaterThanOrEqual(1);
  expect(await page.locator("main").innerText()).toMatch(/at.?most.?one/i);
  expect(await page.locator("main").innerText()).toContain("No claim of a unique or minimal");
  expect(errors).toEqual([]);
  await page.close();
}, 60000);
