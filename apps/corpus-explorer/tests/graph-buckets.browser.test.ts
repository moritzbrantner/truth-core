import { afterAll, beforeAll, expect, test } from "bun:test";
import { chromium, type Browser, type Page } from "playwright";
import path from "node:path";

import { planBuckets } from "../src/lib/graph-bucket-view";
import { getGraphBuckets } from "../src/lib/graph-bucket-data";
import { parseGraphState } from "../src/lib/graph-state";

let browser: Browser;
let server: ReturnType<typeof Bun.serve>;
const root = path.resolve(import.meta.dir, "../out");
const basePath = process.env.TEST_BASE_PATH ?? "";
const screenshots = process.env.NETWORK_SCREENSHOTS;
beforeAll(async () => {
  server = Bun.serve({ port: 0, async fetch(request) {
    let pathname = decodeURIComponent(new URL(request.url).pathname);
    if (basePath) {
      // Like GitHub Pages: nothing is served outside the base path.
      if (!pathname.startsWith(`${basePath}/`)) { return new Response("Not found", { status: 404 }); }
      pathname = pathname.slice(basePath.length);
    }
    const file = path.resolve(root, `.${pathname.endsWith("/") ? `${pathname}index.html` : pathname}`);
    if (!file.startsWith(`${root}${path.sep}`) || !(await Bun.file(file).exists())) { return new Response("Not found", { status: 404 }); }
    return new Response(Bun.file(file));
  } });
  browser = await chromium.launch({ headless: true });
}, 30000);
afterAll(async () => { await browser?.close(); server?.stop(); });

const graphUrl = (query = "") => new URL(`${basePath}/graph/${query ? `?${query}` : ""}`, server.url).toString();

async function open(query = "") {
  const page = await browser.newPage({ viewport: { width: 1440, height: 1000 } });
  const files: string[] = [];
  const errors: string[] = [];
  page.on("request", (request) => {
    const url = new URL(request.url());
    if (url.pathname.includes("/graph-data/")) files.push(url.pathname.split("/").pop() as string);
  });
  page.on("pageerror", (error) => errors.push(error.message));
  await page.goto(graphUrl(query));
  return { page, files, errors };
}

/** Largest distance, in flow units, between an edge end and the centre of its dot. */
async function edgeOffset(page: Page) {
  return page.evaluate(() => {
    const viewport = document.querySelector(".react-flow__viewport") as HTMLElement;
    const matrix = new DOMMatrix(getComputedStyle(viewport).transform);
    const pane = (document.querySelector(".react-flow") as HTMLElement).getBoundingClientRect();
    const centres = new Map<string, { x: number; y: number }>();
    for (const node of document.querySelectorAll<HTMLElement>(".react-flow__node")) {
      const box = (node.querySelector(".network-symbol") ?? node).getBoundingClientRect();
      centres.set(node.dataset.id as string, {
        x: (box.left + box.width / 2 - pane.left - matrix.e) / matrix.a,
        y: (box.top + box.height / 2 - pane.top - matrix.f) / matrix.a,
      });
    }
    let worst = 0;
    let measured = 0;
    for (const edge of document.querySelectorAll<SVGGElement>(".react-flow__edge")) {
      const [source, target] = (edge.getAttribute("data-id") ?? "").split("->");
      const line = edge.querySelector<SVGPathElement>("path.react-flow__edge-path");
      const from = centres.get(source);
      const to = centres.get(target);
      if (!line || !from || !to) continue;
      const start = line.getPointAtLength(0);
      const end = line.getPointAtLength(line.getTotalLength());
      worst = Math.max(worst, Math.hypot(start.x - from.x, start.y - from.y), Math.hypot(end.x - to.x, end.y - to.y));
      measured += 1;
    }
    return { worst, measured };
  });
}

test("default view fetches only the root bucket, and edges meet their dots", async () => {
  const { page, files, errors } = await open();
  await page.locator(".network-marker").first().waitFor();
  await page.waitForLoadState("networkidle");
  const { manifest } = getGraphBuckets();
  expect(files).toEqual(manifest.defaultBuckets.map((id) => `${id}.json`));
  const shell = page.locator(".graph-shell");
  await shell.scrollIntoViewIfNeeded();
  const box = await shell.boundingBox();
  if (!box) throw new Error("Missing graph viewport");
  await page.mouse.move(box.x + box.width / 2, box.y + box.height / 2);
  for (let step = 0; step < 10; step += 1) await page.mouse.wheel(0, -200);
  await page.waitForFunction(() => new DOMMatrix(getComputedStyle(document.querySelector(".react-flow__viewport") as HTMLElement).transform).a > 1);
  await page.waitForTimeout(300);
  const offset = await edgeOffset(page);
  expect(offset.measured).toBeGreaterThan(10);
  // Before #491 every edge ended 15 flow units from its dot (the hit box edge).
  expect(offset.worst).toBeLessThan(2);
  if (screenshots) await shell.screenshot({ path: `${screenshots}/aligned-edges.png` });
  expect(errors).toEqual([]);
  await page.close();
}, 60000);

test("facet filters in the URL fetch only buckets that can match", async () => {
  const { page, files, errors } = await open();
  await page.locator(".network-marker").first().waitFor();
  await page.locator(".frontier-advanced > summary").click();
  await page.getByRole("button", { name: /^Frontier · bare/ }).click();
  await page.waitForURL((url) => url.searchParams.get("closure") === "frontier-bare");
  await page.waitForLoadState("networkidle");
  const { manifest } = getGraphBuckets();
  const expected = planBuckets(manifest, parseGraphState(new URLSearchParams("closure=frontier-bare")), null, null).wanted;
  expect(expected.length).toBeLessThan(manifest.buckets.length);
  expect([...new Set(files)].sort()).toEqual(expected.map((id) => `${id}.json`).sort());
  await page.getByRole("button", { name: /^Lane B/ }).click();
  await page.waitForURL((url) => url.searchParams.get("lane") === "B");
  await page.reload();
  await page.locator(".frontier-advanced > summary").click();
  expect(await page.getByRole("button", { name: /^Lane B/ }).getAttribute("aria-pressed")).toBe("true");
  expect(await page.getByRole("button", { name: /^Frontier · bare/ }).getAttribute("aria-pressed")).toBe("true");
  if (screenshots) await page.locator(".frontier-advanced").screenshot({ path: `${screenshots}/graph-filters.png` });
  expect(errors).toEqual([]);
  await page.close();
}, 60000);

test("buckets load on demand: every bucket, and the bucket of an addressed statement", async () => {
  const { manifest, buckets, graph } = getGraphBuckets();
  const { page, errors } = await open();
  await page.locator(".network-marker").first().waitFor();
  await page.locator(".graph-buckets > summary").click();
  await page.getByRole("button", { name: "Load every bucket", exact: true }).click();
  await page.waitForURL((url) => url.searchParams.get("b") === "all" && url.searchParams.get("islands") === "1");
  await page.waitForFunction((total) => document.querySelectorAll(".react-flow__node").length === total, graph.statements.length + graph.inferences.length);
  if (screenshots) await page.locator(".graph-shell").screenshot({ path: `${screenshots}/all-buckets.png` });
  await page.close();

  const outside = buckets.find((bucket) => bucket.id !== "root" && bucket.inferences.length)!;
  const statement = outside.inferences[0].output;
  const addressed = await open(`sel=${encodeURIComponent(statement)}`);
  await addressed.page.locator(`[data-id="${statement}"] [data-selected="true"]`).waitFor();
  expect(addressed.files).toContain("lookup.json");
  expect(addressed.files).toContain(`${outside.id}.json`);
  expect(addressed.files.filter((file) => file.startsWith("isolated-"))).toEqual([]);
  expect(manifest.defaultBuckets.every((id) => addressed.files.includes(`${id}.json`))).toBe(true);
  expect([...errors, ...addressed.errors]).toEqual([]);
  await addressed.page.close();
}, 60000);
