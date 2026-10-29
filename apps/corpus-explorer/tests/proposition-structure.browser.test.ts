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

test("structure inspector preserves ordered Lean detail and primitive attribute bridge", async () => {
  const page = await browser.newPage({ viewport: { width: 1280, height: 980 } });
  const errors: string[] = [];
  page.on("pageerror", (error) => errors.push(error.message));
  const base = `${server.url}${basePath.replace(/^\//, "")}${basePath ? "/" : ""}`;
  for (const id of ["STMT-CAUSE-PRINCIPLE-BROAD", "STMT-CAUSE-PRINCIPLE-DISTINCT", "STMT-GOD-HAS-CLASSICAL-DIVINE-ATTRIBUTES"]) {
    await page.goto(`${base}statements/${id}/#structure`);
    const inspector = page.getByRole("region", { name: "Proposition structure", exact: true });
    await inspector.locator("[data-structure-inspector] > summary").click();
    expect(await inspector.getByLabel("Expression structure").innerText()).toContain("structural");
    const expansion = inspector.locator("[data-definition-expansion]").first();
    await expansion.locator(":scope > summary").click();
    const body = expansion.locator("details").first();
    await body.locator(":scope > summary").click();
    expect(await body.innerText()).toContain("Type:");
    expect(await body.innerText()).toContain("Parameter binding:");
    if (id.endsWith("DISTINCT")) expect(await expansion.innerText()).toContain("DistinctCausePrinciple");
    if (id.includes("CLASSICAL")) {
      const support = inspector.getByLabel("Proof support and bridge direction");
      expect(await support.innerText()).toContain("STMT-CLASSICAL-ATTRIBUTES-SUFFICE");
      expect(await support.innerText()).toContain("open");
      const interpretation = inspector.getByLabel("Semantic interpretation").locator("details").filter({ has: page.locator('a', { hasText: "DEF-CLASSICAL-ATTRIBUTES-BUNDLE" }) });
      await interpretation.locator(":scope > summary").click();
      expect(await interpretation.innerText()).toContain("Signature.HasClassicalAttributes is still a primitive field");
      expect(await interpretation.innerText()).toContain("one-way premise");
      expect(await inspector.getByLabel("Coverage limits").innerText()).toContain("independent-atom");
      if (process.env.TEST_SCREENSHOT_PATH) {
        await inspector.evaluate((element) => element.scrollIntoView({ block: "start" }));
        await page.screenshot({ path: process.env.TEST_SCREENSHOT_PATH, fullPage: false });
      }
    }
    await page.setViewportSize({ width: 390, height: 844 });
    expect(await inspector.evaluate((element) => element.getBoundingClientRect().right <= window.innerWidth + 1)).toBe(true);
    await page.setViewportSize({ width: 1280, height: 980 });
  }
  await page.goto(`${base}statements/STMT-CATHOLICISM-TRUE/#structure`);
  expect(await page.locator("[data-structure-unavailable]").innerText()).toContain("outside the current published slice");
  expect(errors).toEqual([]);
  await page.close();
}, 60000);
