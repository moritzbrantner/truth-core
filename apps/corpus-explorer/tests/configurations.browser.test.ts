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

test.skipIf(certified)("configuration dossier link preserves named selection and marks static provenance", async () => {
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


test.skipIf(!certified)("certified configurations preserve exact assumptions, cores, witnesses and proof chains", async () => {
  const page = await browser.newPage({ viewport: { width: 1280, height: 900 } });
  const base = `${server.url}${basePath.replace(/^\//, "")}${basePath ? "/" : ""}`;
  await page.goto(`${base}dossiers/STMT-NECESSARY-INDIVIDUAL-DE-DICTO/`);
  await page.getByRole("link", { name: "CONFIG-NECESSARY-INDIVIDUAL", exact: true }).click();
  await page.waitForURL((url) => url.pathname.endsWith("/configurations/CONFIG-NECESSARY-INDIVIDUAL/"));
  await page.getByRole("heading", { name: "model witnessed", exact: true }).waitFor();
  const checkbox = (suffix: string) => page.getByRole("checkbox", { name: new RegExp(`STMT-NECESSARY-INDIVIDUAL-${suffix}`) });
  expect(await checkbox("DE-DICTO").isChecked()).toBe(true);
  expect(await checkbox("INDIVIDUAL-CONTINGENCY").isChecked()).toBe(true);
  await checkbox("DE-RE").check();
  await page.getByRole("heading", { name: "verified incompatible", exact: true }).waitFor();
  expect(await page.getByRole("region", { name: "verified incompatible", exact: true }).innerText()).toContain("NECESSARY-INDIVIDUAL-RE-CONTINGENCY-INCOMPATIBLE");
  expect(await page.getByRole("heading", { name: "Verified conditional applications", exact: true }).count()).toBe(0);
  await checkbox("INDIVIDUAL-CONTINGENCY").uncheck();
  await page.getByRole("heading", { name: "model witnessed", exact: true }).waitFor();
  await checkbox("DE-DICTO").uncheck();
  await page.getByRole("heading", { name: "Verified conditional applications", exact: true }).waitFor();
  expect(await page.getByRole("link", { name: "NECESSARY-INDIVIDUAL-RE-TO-DICTO", exact: true }).count()).toBe(1);
  await checkbox("JOINT-ABSENCE").check();
  await page.getByRole("heading", { name: "verified incompatible", exact: true }).waitFor();
  const core = page.getByRole("region", { name: "verified incompatible", exact: true });
  expect(await core.innerText()).toContain("NECESSARY-INDIVIDUAL-RE-TO-DICTO");
  expect(await core.innerText()).toContain("NECESSARY-INDIVIDUAL-DICTO-JOINT-INCOMPATIBLE");
  expect(await core.innerText()).toContain("inclusion-minimal");
  await core.getByText("Single-premise removal evidence", { exact: true }).click();
  expect(await core.innerText()).toContain("MODEL-NECESSARY-INDIVIDUAL-ALL-PRESENT");
  const url = new URL(page.url());
  expect(url.searchParams.get("set")).toBe("custom");
  expect(url.searchParams.getAll("premise")).toEqual(["STMT-NECESSARY-INDIVIDUAL-DE-RE", "STMT-NECESSARY-INDIVIDUAL-JOINT-ABSENCE"]);
  await page.reload();
  await page.getByRole("heading", { name: "verified incompatible", exact: true }).waitFor();
  expect(await checkbox("DE-RE").isChecked()).toBe(true);
  expect(await checkbox("JOINT-ABSENCE").isChecked()).toBe(true);
  await page.setViewportSize({ width: 390, height: 844 });
  expect(await page.locator("article").evaluate((element) => element.scrollWidth <= element.clientWidth + 1 && element.getBoundingClientRect().right <= window.innerWidth + 1)).toBe(true);
  await page.goto(`${base}configurations/CONFIG-NECESSARY-INDIVIDUAL-NAT-WORLDS/?set=inventory-unresolved`);
  await page.getByRole("heading", { name: "unresolved", exact: true }).waitFor();
  await page.getByText("Models excluded by this profile", { exact: true }).click();
  expect(await page.getByText("W: profile requires Nat; registration uses Bool", { exact: true }).count()).toBe(3);
  await page.getByText("Verification provenance and limits", { exact: true }).click();
  expect(await page.locator("article").innerText()).toContain("Input digest:");
  expect(await page.locator("article").innerText()).toContain("not philosophically distinct theories");
  await page.goto(`${base}configurations/CONFIG-NECESSARY-INDIVIDUAL/?set=custom&premise=STMT-UNKNOWN`);
  await page.getByRole("alert").waitFor();
  expect(await page.getByRole("alert").innerText()).toContain("unsupported");
  expect(await page.getByRole("heading", { name: "model witnessed", exact: true }).count()).toBe(0);
  await page.close();
}, 60000);
