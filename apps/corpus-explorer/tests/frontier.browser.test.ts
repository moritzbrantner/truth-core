import { afterAll, beforeAll, expect, test } from "bun:test";
import { chromium, type Browser } from "playwright";
import path from "node:path";

let browser: Browser;
let server: ReturnType<typeof Bun.serve>;
const root = path.resolve(import.meta.dir, "../out");
const basePath = process.env.TEST_BASE_PATH ?? "";

beforeAll(async () => {
  // Serve the real static export on an OS-assigned port; no mocked corpus or APIs.
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

test("static frontier: queue ↔ graph, goal/global, reload, expansion, focus return, viewport and mobile", async () => {
  const page = await browser.newPage({
    viewport: { width: 1440, height: 1000 },
  });
  const errors: string[] = [];
  page.on("pageerror", (error) => errors.push(error.message));
  await page.goto(`${server.url}${basePath.replace(/^\//, "")}${basePath ? "/" : ""}graph/`);
  await page.getByRole("button", { name: "Global frontier", exact: true }).waitFor();
  const queue = page.getByRole("complementary", {
    name: "Research obligations",
  });
  const globalCount = await queue.locator("ol > li").count();
  expect(globalCount).toBeGreaterThan(50);
  await queue.locator(".research-select").first().click();
  await page.waitForURL((url) => url.searchParams.has("obligation") && url.searchParams.has("sel"));
  const selected = new URL(page.url()).searchParams.get("sel")!;
  const obligation = new URL(page.url()).searchParams.get("obligation")!;
  await page.locator(`[data-id="${selected}"] [data-selected="true"]`).waitFor();
  await page.getByRole("region", { name: "Selected obligation" }).waitFor();
  await page.reload();
  await page.getByRole("region", { name: "Selected obligation" }).waitFor();
  expect(new URL(page.url()).searchParams.get("obligation")).toBe(obligation);
  await page.getByRole("button", { name: "Selected goal frontier", exact: true }).click();
  await page.waitForURL((url) => url.searchParams.get("scope") === "goal");
  expect(await queue.locator("ol > li").count()).toBeLessThan(globalCount);
  await page.getByRole("button", { name: "Global frontier", exact: true }).click();
  await page.waitForURL((url) => !url.searchParams.has("scope"));
  expect(await queue.locator("ol > li").count()).toBe(globalCount);
  // Selecting the graph changes the queue's related-node highlights.
  await queue.locator(".research-select").first().click();
  await page.locator(`[data-id="${selected}"]`).click();
  expect(await queue.locator('[data-related="true"]').count()).toBeGreaterThan(0);
  const overviewUrl = new URL(page.url());
  const savedViewport = await page.locator(".react-flow__viewport").evaluate((element) => {
    const matrix = new DOMMatrixReadOnly(getComputedStyle(element).transform);
    return [matrix.m41, matrix.m42, matrix.a].join(",");
  });
  overviewUrl.searchParams.set("viewport", savedViewport);
  await page.goto(overviewUrl.toString());
  await page.getByRole("button", { name: "Focus here", exact: true }).waitFor();
  const restoredViewport = async () => {
    await page.waitForFunction((saved) => {
      const element = document.querySelector(".react-flow__viewport");
      if (!element) {
        return false;
      }
      const matrix = new DOMMatrixReadOnly(getComputedStyle(element).transform);
      const [x, y, zoom] = saved.split(",").map(Number);
      return Math.abs(matrix.m41 - x) < 0.01 && Math.abs(matrix.m42 - y) < 0.01 && Math.abs(matrix.a - zoom) < 0.0001;
    }, savedViewport);
  };
  await restoredViewport();
  await page.getByRole("button", { name: "Focus here", exact: true }).click();
  await page.waitForURL((url) => url.searchParams.get("view") === "focus");
  await page.getByRole("button", { name: "Expand dependencies and consequences" }).click();
  await page.waitForURL((url) => url.searchParams.getAll("expand").includes(selected));
  const nodeIds = await page
    .locator(".react-flow__node")
    .evaluateAll((nodes) => nodes.map((node) => node.getAttribute("data-id")));
  expect(new Set(nodeIds).size).toBe(nodeIds.length);
  await page.getByRole("button", { name: "Return to overview", exact: true }).click();
  await page.waitForURL((url) => url.searchParams.get("view") !== "focus");
  expect(new URL(page.url()).searchParams.get("sel")).toBe(selected);
  expect(new URL(page.url()).searchParams.get("viewport")).toBe(savedViewport);
  await restoredViewport();
  await page.setViewportSize({ width: 390, height: 844 });
  await page.getByRole("button", { name: "Global frontier", exact: true }).click();
  expect(await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth + 1)).toBe(true);
  expect(errors).toEqual([]);
  await page.close();
}, 60000);
