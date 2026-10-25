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
    await page.locator(".graph-node-cluster").first().waitFor();
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
