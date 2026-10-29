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

test("bounded audit exposes exact scope, open premises and unresolved converse on desktop and touch", async () => {
  const page = await browser.newPage({ viewport: { width: 1280, height: 1000 } });
  const errors: string[] = [];
  page.on("pageerror", (error) => errors.push(error.message));
  const base = `${server.url}${basePath.replace(/^\//, "")}${basePath ? "/" : ""}`;
  await page.goto(`${base}results/CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES/#bundle-audit`);
  const audit = page.getByRole("region", { name: "Bounded bundle audit", exact: true });
  expect(await audit.locator("[data-audit-coverage]").innerText()).toContain("69 record dispositions");
  expect(await audit.innerText()).toContain("25 definitions");
  expect(await audit.innerText()).toContain("No change");
  await audit.locator("[data-audit-records] > summary").click();
  expect(await audit.locator("li").count()).toBeGreaterThanOrEqual(69);
  const open = audit.locator("li").filter({ has: page.locator("a", { hasText: "STMT-CAUSE-OF-QUALITY-IN-ANOTHER-IS-MORE-SUCH" }) });
  expect((await open.innerText()).toLowerCase()).toContain("unresolved");
  expect(await open.innerText()).toContain("removed its Aristotle attribution");
  await audit.locator("[data-audit-records] > summary").click();
  const limits = audit.getByLabel("Audit limits and unresolved bridges");
  expect(await limits.innerText()).toContain("IsGod need not be inhabited");
  expect(await limits.innerText()).toContain("#720");
  expect(await limits.innerText()).toContain("no declared disjunction-elimination use");
  if (process.env.TEST_SCREENSHOT_PATH) await audit.screenshot({ path: process.env.TEST_SCREENSHOT_PATH });
  await page.close();
  const touch = await browser.newContext({ viewport: { width: 390, height: 844 }, isMobile: true, hasTouch: true });
  const mobile = await touch.newPage();
  await mobile.goto(`${base}results/CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES/#bundle-audit`);
  const panel = mobile.getByRole("region", { name: "Bounded bundle audit", exact: true });
  await panel.locator("[data-audit-records] > summary").tap();
  expect(await panel.locator("[data-audit-records]").evaluate((e) => e.hasAttribute("open"))).toBe(true);
  expect(await panel.evaluate((e) => e.getBoundingClientRect().right <= window.innerWidth + 1)).toBe(true);
  expect(await mobile.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth + 1)).toBe(true);
  await touch.close();
  expect(errors).toEqual([]);
}, 60000);

test("complete specialization and consumers expose same-witness and identity boundaries", async () => {
  const base = `${server.url}${basePath.replace(/^\//, "")}${basePath ? "/" : ""}`;
  const page = await browser.newPage({ viewport: { width: 1280, height: 1000 } });
  const errors: string[] = [];
  page.on("pageerror", (error) => errors.push(error.message));
  for (const id of ["CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES-ALL", "CATHOLICISM-STAGES-ONE-TWO-SAME-WITNESS", "CATHOLICISM-STAGES-ONE-TWO-Q11-NATURE", "CATHOLICISM-QUARTA-VIA-CLASSICAL-WITNESS", "CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES-IDENTITY"]) {
    await page.goto(`${base}results/${id}/#bundle-audit`);
    const panel = page.getByRole("region", { name: "Bounded bundle audit", exact: true });
    expect(await panel.locator("[data-audit-coverage]").innerText()).toContain("149 record dispositions");
    expect(await panel.innerText()).toContain("DecidableEq Principle");
    expect(await panel.innerText()).toContain("same witness");
    expect(await panel.innerText()).toContain("Q11-NATURE");
    await panel.locator("[data-audit-records] > summary").click();
    const immutable = panel.locator("li").filter({ has: page.locator("a", { hasText: "STMT-GOD-IS-IMMUTABLE" }) });
    expect(await immutable.innerText()).toContain("IsImmutable InPotency");
    expect(await immutable.innerText()).toContain("same Respect");
    await panel.locator("[data-audit-records] > summary").click();
    if (id.endsWith("-ALL") && process.env.TEST_COMPLETE_SCREENSHOT_PATH) {
      await panel.screenshot({ path: process.env.TEST_COMPLETE_SCREENSHOT_PATH });
    }
  }
  await page.close();
  const context = await browser.newContext({ viewport: { width: 390, height: 844 }, isMobile: true, hasTouch: true });
  const mobile = await context.newPage();
  await mobile.goto(`${base}results/CATHOLICISM-STAGE2-CLASSICAL-ATTRIBUTES-ALL/#bundle-audit`);
  const panel = mobile.getByRole("region", { name: "Bounded bundle audit", exact: true });
  await panel.locator("[data-audit-records] > summary").tap();
  expect(await panel.locator("[data-audit-records]").evaluate((e) => e.hasAttribute("open"))).toBe(true);
  expect(await mobile.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth + 1)).toBe(true);
  await context.close();
  expect(errors).toEqual([]);
}, 60000);
