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

test("configuration dossier link preserves named selection and marks static provenance", async () => {
  const page = await browser.newPage({ viewport: { width: 1280, height: 900 } });
  const base = `${server.url}${basePath.replace(/^\//, "")}${basePath ? "/" : ""}`;
  await page.goto(`${base}dossiers/STMT-NECESSARY-INDIVIDUAL-DE-DICTO/`);
  await page.getByRole("link", { name: "CONFIG-NECESSARY-INDIVIDUAL", exact: true }).click();
  await page.waitForURL((url) => url.pathname.endsWith("/configurations/CONFIG-NECESSARY-INDIVIDUAL/"));
  await page.getByRole("heading", { name: "Configuration assumptions", level: 1, exact: true }).waitFor();
  expect(await page.getByText("Registered provenance · verification required", { exact: true }).count()).toBe(1);
  await page.getByRole("navigation", { name: "Named assumption sets" }).getByRole("link", { name: "varying-bearers-control", exact: true }).click();
  expect(new URL(page.url()).hash).toBe("#varying-bearers-control");
  const control = page.getByRole("region", { name: "varying-bearers-control", exact: true });
  expect(await control.innerText()).toContain("MODEL-NECESSARY-INDIVIDUAL-ALTERNATING");
  await control.getByText("Verify this assumption set", { exact: true }).click();
  expect(await control.innerText()).toContain("--premise STMT-NECESSARY-INDIVIDUAL-DE-DICTO");
  await page.reload();
  expect(new URL(page.url()).hash).toBe("#varying-bearers-control");
  await page.setViewportSize({ width: 390, height: 844 });
  expect(await page.locator("article").evaluate((element) => element.scrollWidth <= element.clientWidth + 1 && element.getBoundingClientRect().right <= window.innerWidth + 1)).toBe(true);
  await page.goto(`${base}configurations/CONFIG-NECESSARY-INDIVIDUAL-NAT-WORLDS/`);
  await page.getByText("Models excluded by this profile", { exact: true }).click();
  expect(await page.getByText("W: profile requires Nat; registration uses Bool", { exact: true }).count()).toBe(3);
  await page.close();
}, 60000);
