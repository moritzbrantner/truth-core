import { afterAll, beforeAll, expect, test } from "bun:test";
import path from "node:path";
import { chromium, type Browser } from "playwright";
import { uid } from "./corpus-records";
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
      return await artifact.exists() ? new Response(artifact) : new Response("Not found", { status: 404 });
    },
  });
  browser = await chromium.launch({ headless: true });
}, 30000);

afterAll(async () => {
  await browser?.close();
  server?.stop();
});


test("progress search drills into canonical comparison and evidence with deployment prefix", async () => {
  const page = await browser.newPage();
  const errors: string[] = [];
  page.on("pageerror", (error) => errors.push(error.message));
  await page.goto(new URL(`${basePath}/progress/`, server.url).toString());
  await page.getByRole("heading", { name: "Research progress", exact: true }).waitFor();
  await page.getByLabel("Find proposition, argument or sense").fill("NECESSARY_1");
  expect(await page.getByText("0 matching propositions", { exact: true }).count()).toBe(0);
  const id = uid("statement", "STMT-ACT-SIMPLY-PRIOR-TO-POTENCY");
  await page.getByLabel("Find proposition, argument or sense").fill(id);
  await page.getByText("1 matching propositions", { exact: true }).waitFor();
  await page.getByRole("combobox").selectOption("established");
  await page.getByText("0 matching propositions", { exact: true }).waitFor();
  await page.getByRole("combobox").selectOption("open");
  await page.getByText("1 matching propositions", { exact: true }).waitFor();
  await page.locator(`a[href="${basePath}/dossiers/${id}/#research-comparison"]`).click();
  await page.getByRole("heading", { name: "Sense and rival comparison", exact: true }).waitFor();
  expect(new URL(page.url()).pathname).toBe(`${basePath}/dossiers/${id}/`);
  expect(await page.getByText("Not established.", { exact: false }).count()).toBeGreaterThan(0);
  await page.getByRole("heading", { name: "Remaining gap and next step", exact: true }).waitFor();
  const proof = page.locator('article a[href*="/results/"]').first();
  expect(await proof.count()).toBe(1);
  await proof.click();
  await page.getByRole("heading", { name: "The advertised theorem", exact: true }).waitFor();
  await page.goto(new URL(`${basePath}/dossiers/${id}/#research-comparison`, server.url).toString());
  const definition = page.locator('#research-comparison a[href*="/definitions/"]').first();
  await definition.click();
  await page.waitForURL((url) => url.pathname.startsWith(`${basePath}/definitions/`));
  await page.reload();
  expect(errors).toEqual([]);
  await page.close();
}, 60000);
