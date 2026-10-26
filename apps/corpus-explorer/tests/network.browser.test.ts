import { afterAll, beforeAll, expect, test } from "bun:test";
import { chromium, type Browser } from "playwright";
import path from "node:path";
import { getPropositionGraph } from "../src/lib/proposition-graph-data";

let browser: Browser;
let server: ReturnType<typeof Bun.serve>;
const root = path.resolve(import.meta.dir, "../out");
const basePath = process.env.TEST_BASE_PATH ?? "";
const screenshots = process.env.NETWORK_SCREENSHOTS;
beforeAll(async () => {
  server = Bun.serve({ port: 0, async fetch(request) {
    let pathname = decodeURIComponent(new URL(request.url).pathname);
    if (basePath && pathname.startsWith(`${basePath}/`)) { pathname = pathname.slice(basePath.length); }
    const file = path.resolve(root, `.${pathname.endsWith("/") ? `${pathname}index.html` : pathname}`);
    if (!file.startsWith(`${root}${path.sep}`) || !(await Bun.file(file).exists())) { return new Response("Not found", { status: 404 }); }
    return new Response(Bun.file(file));
  } });
  browser = await chromium.launch({ headless: true });
}, 30000);
afterAll(async () => { await browser?.close(); server?.stop(); });

for (const mobile of [false, true]) {
  test(`real corpus network: ${mobile ? "mobile touch" : "desktop keyboard"}, layered comparison, focus return and stable layout`, async () => {
    const page = await browser.newPage({ viewport: mobile ? { width: 390, height: 844 } : { width: 1440, height: 1000 }, hasTouch: mobile, isMobile: mobile });
    const errors: string[] = [];
    page.on("pageerror", (error) => errors.push(error.message));
    const start = performance.now();
    const url = new URL(`${basePath}/graph/`, server.url);
    await page.goto(url.toString());
    const shell = page.locator(".graph-shell");
    await page.locator(".network-marker").first().waitFor();
    await shell.scrollIntoViewIfNeeded();
    const mounted = await page.locator(".network-marker").count();
    expect(mounted).toBeGreaterThan(1000);
    const corpus = getPropositionGraph();
    expect(mounted).toBeLessThanOrEqual(corpus.statements.length + corpus.inferences.length);
    const initialMs = Math.round(performance.now() - start);
    if (screenshots) { await shell.screenshot({ path: `${screenshots}/${mobile ? "mobile" : "desktop"}-network.png` }); }
    if (!mobile) {
      const keyboardNode = page.locator(".react-flow__node-marker").first();
      const keyboardId = await keyboardNode.getAttribute("data-id");
      await keyboardNode.focus();
      await page.keyboard.press("Enter");
      await page.waitForURL((location) => location.searchParams.get("sel") === keyboardId);
    }
    const queue = page.getByRole("complementary", { name: "Research obligations" });
    const interaction = performance.now();
    const beforeQueue = page.url();
    await queue.locator(".research-select").first().click();
    await page.waitForURL((location) => location.searchParams.has("obligation") && location.toString() !== beforeQueue);
    const selected = new URL(page.url()).searchParams.get("sel")!;
    const marker = page.locator(`[data-id="${selected}"]`);
    await marker.locator('[data-selected="true"]').waitFor();
    await marker.scrollIntoViewIfNeeded();
    if (mobile) { await marker.tap(); }
    else {
      await marker.focus();
      await page.keyboard.press("Enter");
      expect(await marker.getAttribute("tabindex")).toBe("0");
    }
    const selectionMs = Math.round(performance.now() - interaction);
    await page.getByText(/Each application requires all its premises/).waitFor();
    await page.getByRole("button", { name: "Focus here", exact: true }).click();
    await page.waitForURL((location) => location.searchParams.get("view") === "focus");
    expect(await page.locator(".graph-node-statement").count()).toBeGreaterThan(0);
    await page.getByRole("button", { name: "Return to overview", exact: true }).click();
    await page.waitForURL((location) => location.searchParams.get("view") !== "focus");
    await marker.locator(".network-marker").waitFor();
    await shell.scrollIntoViewIfNeeded();
    await page.getByRole("button", { name: /^zoom in$/i }).click();
    const box = await shell.boundingBox();
    if (!box) { throw new Error("Missing graph viewport"); }
    await page.mouse.move(box.x + box.width / 2, box.y + box.height / 2);
    await page.mouse.wheel(0, -100);
    if (mobile) {
      const cdp = await page.context().newCDPSession(page);
      const x = Math.round(box.x + box.width / 2);
      const y = Math.round(box.y + Math.min(box.height / 2, 200));
      await cdp.send("Input.dispatchTouchEvent", { type: "touchStart", touchPoints: [{ x: x - 20, y }, { x: x + 20, y }] });
      await cdp.send("Input.dispatchTouchEvent", { type: "touchMove", touchPoints: [{ x: x - 10, y: y + 30 }, { x: x + 50, y: y + 30 }] });
      await cdp.send("Input.dispatchTouchEvent", { type: "touchEnd", touchPoints: [] });
      await cdp.detach();
    } else {
      await page.mouse.move(box.x + 12, box.y + 12);
      await page.mouse.down();
      await page.mouse.move(box.x + 70, box.y + 45, { steps: 5 });
      await page.mouse.up();
    }
    await page.waitForURL((location) => location.searchParams.has("viewport"));
    const transform = await marker.getAttribute("style");
    // A settled network owns no animation: frames cannot change node positions.
    await page.waitForTimeout(350);
    expect(await marker.getAttribute("style")).toBe(transform);
    await page.getByRole("button", { name: "Layered", exact: true }).click();
    await page.waitForURL((location) => location.searchParams.get("layout") === "layered");
    // The selected cluster is expanded and centered; other clusters may be
    // virtualized outside this viewport. Check the selected statement instead.
    await shell.scrollIntoViewIfNeeded();
    await marker.locator('.graph-node-statement[data-selected="true"]').waitFor();
    const layeredBox = await shell.boundingBox();
    const selectedBox = await marker.boundingBox();
    if (!layeredBox || !selectedBox) { throw new Error("Missing layered selection geometry"); }
    expect(selectedBox.x).toBeGreaterThanOrEqual(layeredBox.x);
    expect(selectedBox.y).toBeGreaterThanOrEqual(layeredBox.y);
    expect(selectedBox.x + selectedBox.width).toBeLessThanOrEqual(layeredBox.x + layeredBox.width);
    expect(selectedBox.y + selectedBox.height).toBeLessThanOrEqual(layeredBox.y + layeredBox.height);
    const comparison = new URL(page.url());
    comparison.searchParams.delete("viewport");
    comparison.searchParams.delete("sel");
    comparison.searchParams.delete("obligation");
    for (const key of new Set(getPropositionGraph().statements.map((node) => node.clusters.passage))) { comparison.searchParams.append("open", key); }
    await page.goto(comparison.toString());
    await page.locator(".graph-node-statement").first().waitFor();
    await shell.scrollIntoViewIfNeeded();
    if (screenshots) { await shell.screenshot({ path: `${screenshots}/${mobile ? "mobile" : "desktop"}-layered.png` }); }
    console.info(JSON.stringify({ workload: "real-corpus-network-browser", mobile, mounted, initialMs, selectionMs, browser: browser.version(), bun: Bun.version }));
    expect(errors).toEqual([]);
    await page.close();
  }, 60000);
}

test("frontier is the homepage: dot statuses, direct workspace, and durable emphasis", async () => {
  const page = await browser.newPage({ viewport: { width: 1440, height: 900 } });
  const errors: string[] = [];
  page.on("pageerror", (error) => errors.push(error.message));
  await page.goto(new URL(`${basePath}/`, server.url).toString());
  await page.getByRole("heading", { name: "Epistemic frontier" }).waitFor();
  await page.locator(".network-marker[data-kind='statement']").first().waitFor();
  expect(await page.locator(".network-marker[data-frontier='true']").count()).toBeGreaterThan(0);
  expect(await page.locator(".network-marker[data-frontier-depth='bare']").count()).toBeGreaterThan(0);
  expect(await page.locator(".network-marker[data-established='true']").count()).toBeGreaterThan(0);
  const established = page.locator('.network-marker[data-established="true"][data-dimmed="false"]:not([data-selected="true"])').first();
  expect(await established.evaluate((element) => getComputedStyle(element).opacity)).toBe("0.85");
  expect(await page.locator(".network-marker[data-kind='inference']").count()).toBeGreaterThan(0);
  expect(await page.locator(".frontier-map-key").isVisible()).toBe(true);
  expect(await page.getByRole("link", { name: "Case", exact: true }).getAttribute("href")).toContain("/state");
  const count = await page.locator(".network-marker[data-frontier='true']").count();
  await page.getByRole("button", { name: "Frontier highlighted" }).click();
  await page.waitForURL((url) => url.searchParams.get("emphasis") === "all");
  await page.reload();
  expect(await page.getByRole("button", { name: "Show all equally" }).getAttribute("aria-pressed")).toBe("false");
  expect(await page.locator(".network-marker[data-frontier='true']").count()).toBe(count);
  await page.goto(new URL(`${basePath}/?q=no-statement-has-this-query`, server.url).toString());
  const dimmedEstablished = page.locator('.network-marker[data-established="true"][data-dimmed="true"]').first();
  await dimmedEstablished.waitFor();
  expect(await dimmedEstablished.evaluate((element) => getComputedStyle(element).opacity)).toBe("0.16");
  expect(errors).toEqual([]);
  await page.close();
}, 60000);

test("recorded claim evidence links related propositions without changing proof controls", async () => {
  const projected = getPropositionGraph().relations.find((relation) => relation.originKind === "claim" && relation.subject !== relation.object);
  if (!projected) { throw new Error("The corpus needs an inspectable claim evidence relation"); }
  const page = await browser.newPage({ viewport: { width: 1440, height: 900 } });
  const url = new URL(`${basePath}/`, server.url);
  url.searchParams.set("sel", projected.subject);
  await page.goto(url.toString());
  await page.locator(".network-marker[data-kind='statement']").first().waitFor();
  await page.locator(".graph-detail").getByRole("link", { name: `${projected.originId} →`, exact: true }).first().waitFor();
  expect(await page.locator('.react-flow__edge[data-id^="relation:"]').count()).toBeGreaterThan(0);
  await page.locator(".frontier-advanced > summary").click();
  await page.getByRole("checkbox", { name: "Recorded research links (not proof)" }).uncheck();
  await page.waitForURL((location) => location.searchParams.get("relations") === "0");
  expect(await page.locator('.react-flow__edge[data-id^="relation:"]').count()).toBe(0);
  expect(await page.locator(".network-marker[data-kind='inference']").count()).toBeGreaterThan(0);
  await page.reload();
  await page.locator(".frontier-advanced > summary").click();
  expect(await page.getByRole("checkbox", { name: "Recorded research links (not proof)" }).isChecked()).toBe(false);
  await page.close();
}, 60000);
