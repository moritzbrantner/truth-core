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

test("truth pilot: logical scope, open bridges, reciprocal comparison and scoped frontier navigation", async () => {
  const page = await browser.newPage({ viewport: { width: 1440, height: 1000 } });
  const errors: string[] = [];
  page.on("pageerror", (error) => errors.push(error.message));
  const base = `${server.url}${basePath.replace(/^\//, "")}${basePath ? "/" : ""}`;
  await page.goto(`${base}objective-truth/`);
  await page.getByRole("heading", { name: "The two logical propositions", exact: true }).waitFor();
  const logical = page.locator("section").filter({ has: page.getByRole("heading", { name: "The two logical propositions", exact: true }) });
  expect(await logical.getByText("Proved · established", { exact: true }).count()).toBe(2);
  const bridge = page.locator("section").filter({ has: page.getByRole("heading", { name: "Interpretation bridges still to defend", exact: true }) });
  expect(await bridge.getByText("Open · bare", { exact: true }).count()).toBe(2);
  const table = page.getByRole("table", { name: "Authoritative frontier calculation for the reciprocal-entailment fixture" });
  expect(await table.getByText("Neither", { exact: true }).count()).toBe(2);
  expect(await table.getByText("A and B", { exact: true }).count()).toBe(1);
  await bridge.getByRole("link", { name: "Inspect graph and frontier", exact: true }).first().click();
  await page.waitForURL((url) => url.searchParams.get("target") === "STMT-PILOT-LOGICAL-SENTENCE-STABLE");
  await page.getByRole("button", { name: "Selected goal frontier", exact: true }).waitFor();
  const queue = page.getByRole("complementary", { name: "Research obligations" });
  expect(await queue.innerText()).toContain("logical sentence");
  await page.reload();
  await queue.waitFor();
  expect(new URL(page.url()).searchParams.get("sel")).toBe("STMT-PILOT-LOGICAL-SENTENCE-STABLE");
  await page.goto(`${base}objective-truth/`);
  await page.setViewportSize({ width: 390, height: 844 });
  expect(await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth + 1)).toBe(true);
  expect(errors).toEqual([]);
  await page.close();
}, 60000);
