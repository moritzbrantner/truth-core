import { afterAll, beforeAll, expect, test } from "bun:test";
import path from "node:path";
import { chromium, type Browser } from "playwright";

let browser: Browser;
let server: ReturnType<typeof Bun.serve>;
const root = path.resolve(import.meta.dir, "../out");
const basePath = process.env.TEST_BASE_PATH ?? "";
const certified = process.env.TRUTH_CORE_REQUIRE_CONFIGURATION_REPORT === "true";

beforeAll(async () => {
  server = Bun.serve({
    port: 0,
    async fetch(request) {
      const requested = decodeURIComponent(new URL(request.url).pathname);
      const pathname = basePath && requested.startsWith(`${basePath}/`) ? requested.slice(basePath.length) : requested;
      const relative = pathname.endsWith("/") ? `${pathname}index.html` : pathname;
      const file = path.resolve(root, `.${relative}`);
      if (!file.startsWith(`${root}${path.sep}`)) { return new Response("Not found", { status: 404 }); }
      const artifact = Bun.file(file);
      if (!(await artifact.exists())) { return new Response("Not found", { status: 404 }); }
      return new Response(artifact);
    },
  });
  browser = await chromium.launch({ headless: true });
}, 30000);

afterAll(async () => {
  await browser?.close();
  server?.stop();
});

test("atlas's five lenses use the current static reports, expose evidence, and preserve URL navigation", async () => {
  const page = await browser.newPage({ viewport: { width: 1360, height: 900 } });
  const base = `${server.url}${basePath.replace(/^\//, "")}${basePath ? "/" : ""}`;
  await page.goto(`${base}atlas/`);
  await page.getByRole("heading", { name: "Progress atlas", exact: true }).waitFor();
  const navigation = page.getByRole("navigation", { name: "Atlas visualizations" });
  expect(await navigation.getByRole("button").count()).toBe(5);
  if (certified) {
    await page.getByRole("group", { name: /Incompatible cores connected/ }).waitFor();
    expect(await page.getByRole("link", { name: /^STMT-/ }).count()).toBeGreaterThan(0);
  } else {
    await page.getByRole("region", { name: "Certification unavailable" }).waitFor();
  }

  await navigation.getByRole("button", { name: /Configuration space/ }).click();
  await page.waitForURL((url) => url.searchParams.get("view") === "mosaic");
  if (certified) {
    await page.getByRole("region", { name: "Certified configuration mosaic" }).waitFor();
    const first = page.getByRole("button", { name: /^Selection \d+:/ }).first();
    await first.click();
    await page.waitForURL((url) => url.searchParams.has("mask"));
  } else {
    expect(await page.getByRole("region", { name: "Certification unavailable" }).count()).toBe(1);
  }

  await navigation.getByRole("button", { name: /Proof routes/ }).click();
  await page.getByRole("region", { name: "Compare conditional proof routes" }).waitFor();
  const routes = page.getByRole("region", { name: "Compare conditional proof routes" }).getByRole("button");
  expect(await routes.count()).toBeGreaterThan(0);
  await routes.last().click();
  await page.waitForURL((url) => url.searchParams.has("route"));

  await navigation.getByRole("button", { name: /Frontier treemap/ }).click();
  await page.getByRole("region", { name: "Open-premise treemap" }).waitFor();
  await page.getByRole("region", { name: "Open-premise treemap" }).getByRole("button").last().click();
  await page.waitForURL((url) => url.searchParams.get("group") === "other-sourced");

  await navigation.getByRole("button", { name: /Impact waves/ }).click();
  await page.getByText("Hypothetical challenge / recorded dependencies").waitFor();
  const picker = page.getByLabel("Challenge an open premise");
  expect(await picker.locator("option").count()).toBeGreaterThan(0);
  const option = await picker.locator("option").last().getAttribute("value");
  if (option) { await picker.selectOption(option); }
  await page.waitForURL((url) => url.searchParams.get("premise") === option);
  await page.reload();
  await page.getByText("Hypothetical challenge / recorded dependencies").waitFor();

  await page.setViewportSize({ width: 390, height: 844 });
  expect(await page.locator(".atlas-page").evaluate((element) => element.getBoundingClientRect().right <= window.innerWidth + 1)).toBe(true);
  await page.close();
}, 90000);
